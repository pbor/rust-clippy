use clippy_config::Conf;
use clippy_utils::SpanlessEq;
use clippy_utils::diagnostics::span_lint_and_sugg;
use clippy_utils::msrvs::{self, Msrv};
use clippy_utils::res::MaybeDef;
use clippy_utils::source::snippet;
use clippy_utils::visitors::is_local_used;
use rustc_ast::LitKind;
use rustc_errors::Applicability;
use rustc_hir::{Expr, ExprKind, PatKind, RustcVersion};
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::impl_lint_pass;
use rustc_span::{Span, Symbol, sym};
use std::fmt;

declare_clippy_lint! {
    /// ### What it does
    /// Checks for code to be replaced by `pop_if` methods.
    ///
    /// ### Why is this bad?
    /// Using `pop_if` is shorter and more idiomatic.
    ///
    /// ### Examples
    ///
    /// ```no_run
    /// # let mut vec = vec![1, 2, 3, 4, 5];
    /// if vec.last().is_some_and(|x| *x > 5) {
    ///     vec.pop().unwrap();
    /// }
    /// ```
    /// Use instead:
    /// ```
    /// vec.pop_if(|x| *x > 5);
    /// ```
    ///
    /// ```no_run
    /// # use std::collections::VecDeque;
    /// # let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3, 4, 5]);
    /// if deque.back().is_some_and(|x| *x > 5) {
    ///     deque.pop_back().unwrap();
    /// }
    /// if deque.front().is_some_and(|x| *x > 5) {
    ///     deque.pop_front().unwrap();
    /// }
    /// ```
    /// Use instead:
    /// ```
    /// deque.pop_back_if(|x| *x > 5);
    /// deque.pop_front_if(|x| *x > 5);
    /// ```
    #[clippy::version = "1.95.0"]
    pub MANUAL_POP_IF,
    style,
    "manual implementation of `pop_if` methods"
}

pub struct ManualPopIf {
    msrv: Msrv,
}

impl ManualPopIf {
    pub fn new(conf: &'static Conf) -> Self {
        Self { msrv: conf.msrv }
    }
}

impl_lint_pass!(ManualPopIf => [MANUAL_POP_IF]);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CollectionMethod {
    VecPopIf,
    VecDequePopBackIf,
    VecDequePopFrontIf,
}

impl CollectionMethod {
    fn check_method(self) -> &'static str {
        match self {
            CollectionMethod::VecPopIf => "last",
            CollectionMethod::VecDequePopBackIf => "back",
            CollectionMethod::VecDequePopFrontIf => "front",
        }
    }

    fn pop_method(self) -> &'static str {
        match self {
            CollectionMethod::VecPopIf => "pop",
            CollectionMethod::VecDequePopBackIf => "pop_back",
            CollectionMethod::VecDequePopFrontIf => "pop_front",
        }
    }

    fn pop_if_method(self) -> &'static str {
        match self {
            CollectionMethod::VecPopIf => "pop_if",
            CollectionMethod::VecDequePopBackIf => "pop_back_if",
            CollectionMethod::VecDequePopFrontIf => "pop_front_if",
        }
    }

    fn msrv(self) -> RustcVersion {
        match self {
            CollectionMethod::VecPopIf => msrvs::VEC_POP_IF,
            CollectionMethod::VecDequePopBackIf => msrvs::VEC_DEQUE_POP_BACK_IF,
            CollectionMethod::VecDequePopFrontIf => msrvs::VEC_DEQUE_POP_FRONT_IF,
        }
    }
}

impl fmt::Display for CollectionMethod {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CollectionMethod::VecPopIf => write!(f, "`Vec::pop_if`"),
            CollectionMethod::VecDequePopBackIf => write!(f, "`VecDeque::pop_back_if`"),
            CollectionMethod::VecDequePopFrontIf => write!(f, "`VecDeque::pop_front_if`"),
        }
    }
}

/// Represents a detected manual `pop_if` pattern
///
/// This struct holds all the information needed to emit a lint diagnostic
/// and generate a suggestion for replacing manual conditional pop patterns
/// with the idiomatic `pop_if` methods.
struct ManualPopIfPattern<'tcx> {
    /// The collection being operated on (e.g., `vec` in `vec.last()`)
    collection_expr: &'tcx Expr<'tcx>,

    /// The condition closure/expression that determines whether to pop
    /// (e.g., `*x > 5` in `|x| *x > 5`)
    predicate: &'tcx Expr<'tcx>,

    /// Parameter name for the closure (e.g., `x` in `|x| *x > 5`)
    param_name: Symbol,

    /// Span of the entire if expression (including the `if` keyword)
    if_span: Span,

    /// The type of collection method (VecPopIf, VecDequePopBackIf, or VecDequePopFrontIf)
    collection_type: CollectionMethod,
}

impl ManualPopIf {
    fn pop_value_is_used(then_block: &Expr<'_>) -> bool {
        let ExprKind::Block(block, _) = then_block.kind else {
            return true;
        };

        if block.expr.is_some() {
            return true;
        }

        if let [stmt] = block.stmts {
            match stmt.kind {
                rustc_hir::StmtKind::Semi(inner_expr) => {
                    if let ExprKind::MethodCall(path, _, _, _) = inner_expr.kind
                        && path.ident.name == sym::unwrap
                    {
                        return false;
                    }
                    return false;
                },
                rustc_hir::StmtKind::Expr(_) | rustc_hir::StmtKind::Let(_) => return true,
                rustc_hir::StmtKind::Item(_) => return false,
            }
        }

        if let Some(last_stmt) = block.stmts.last() {
            return matches!(last_stmt.kind, rustc_hir::StmtKind::Expr(_));
        }

        false
    }

    fn check_is_some_and_pattern<'tcx>(
        &self,
        cx: &LateContext<'tcx>,
        cond: &'tcx Expr<'_>,
        then_block: &'tcx Expr<'_>,
        if_expr_span: Span,
        collection_type: CollectionMethod,
    ) -> Option<ManualPopIfPattern<'tcx>> {
        let check_method = collection_type.check_method();
        let pop_method = collection_type.pop_method();

        // Match: collection.check_method().is_some_and(|x| condition(x))
        if let ExprKind::MethodCall(path, receiver, args, _) = cond.kind
            && path.ident.as_str() == "is_some_and"
            && let ExprKind::MethodCall(check_path, collection_expr, _, _) = receiver.kind
            && check_path.ident.as_str() == check_method
            && Self::is_collection_type(cx, collection_expr, collection_type)
            && let [closure_arg] = args
            && let ExprKind::Closure(closure) = closure_arg.kind
        {
            let body = cx.tcx.hir_body(closure.body);
            let predicate = body.value;

            // Check then block contains collection.pop_method().unwrap()
            if let Some((pop_collection, _pop_span)) = Self::check_pop_unwrap(then_block, pop_method)
                && exprs_are_same(cx, collection_expr, pop_collection)
            {
                let param_name = if let [param] = body.params
                    && let Some(ident) = param.pat.simple_ident()
                {
                    ident.name
                } else {
                    return None;
                };

                return Some(ManualPopIfPattern {
                    collection_expr,
                    predicate,
                    param_name,
                    if_span: if_expr_span,
                    collection_type,
                });
            }
        }

        None
    }

    fn check_if_let_pattern<'tcx>(
        &self,
        cx: &LateContext<'tcx>,
        cond: &'tcx Expr<'_>,
        then_block: &'tcx Expr<'_>,
        if_expr_span: Span,
        collection_type: CollectionMethod,
    ) -> Option<ManualPopIfPattern<'tcx>> {
        let check_method = collection_type.check_method();
        let pop_method = collection_type.pop_method();

        // Match: if let Some(x) = collection.check_method()
        if let ExprKind::Let(let_expr) = cond.kind
            && let PatKind::TupleStruct(qpath, [binding_pat], _) = let_expr.pat.kind
            && let res = cx.qpath_res(&qpath, let_expr.pat.hir_id)
            && cx.tcx.lang_items().get(rustc_hir::LangItem::OptionSome) == res.opt_def_id()
            && let PatKind::Binding(_, binding_id, binding_name, _) = binding_pat.kind
            && let ExprKind::MethodCall(path, collection_expr, _, _) = let_expr.init.kind
            && path.ident.as_str() == check_method
            && Self::is_collection_type(cx, collection_expr, collection_type)
            && let ExprKind::Block(block, _) = then_block.kind
            && let [inner_if_stmt] = block.stmts
            && let rustc_hir::StmtKind::Expr(inner_if) | rustc_hir::StmtKind::Semi(inner_if) = inner_if_stmt.kind
            && let ExprKind::If(inner_cond, inner_then, None) = inner_if.kind
            && is_local_used(cx, inner_cond, binding_id)
            && let Some((pop_collection, _pop_span)) = Self::check_pop_unwrap(inner_then, pop_method)
            && exprs_are_same(cx, collection_expr, pop_collection)
        {
            return Some(ManualPopIfPattern {
                collection_expr,
                predicate: inner_cond,
                param_name: binding_name.name,
                if_span: if_expr_span,
                collection_type,
            });
        }

        None
    }

    fn check_map_unwrap_or_pattern<'tcx>(
        &self,
        cx: &LateContext<'tcx>,
        cond: &'tcx Expr<'_>,
        then_block: &'tcx Expr<'_>,
        if_expr_span: Span,
        collection_type: CollectionMethod,
    ) -> Option<ManualPopIfPattern<'tcx>> {
        let check_method = collection_type.check_method();
        let pop_method = collection_type.pop_method();

        // Match: collection.check_method().map(|x| condition(x)).unwrap_or(false)
        if let ExprKind::MethodCall(unwrap_path, receiver, unwrap_args, _) = cond.kind
            && unwrap_path.ident.name == sym::unwrap_or
            && let [default_arg] = unwrap_args
            && matches!(default_arg.kind, ExprKind::Lit(lit) if matches!(lit.node, LitKind::Bool(false)))
            && let ExprKind::MethodCall(map_path, map_receiver, map_args, _) = receiver.kind
            && map_path.ident.name == sym::map
            && let ExprKind::MethodCall(check_path, collection_expr, _, _) = map_receiver.kind
            && check_path.ident.as_str() == check_method
            && Self::is_collection_type(cx, collection_expr, collection_type)
            && let [closure_arg] = map_args
            && let ExprKind::Closure(closure) = closure_arg.kind
        {
            let body = cx.tcx.hir_body(closure.body);
            let predicate = body.value;

            // Verify the map closure returns a boolean type
            let predicate_ty = cx.typeck_results().expr_ty(predicate);
            if !predicate_ty.is_bool() {
                return None;
            }

            // Check then block contains collection.pop_method().unwrap()
            if let Some((pop_collection, _pop_span)) = Self::check_pop_unwrap(then_block, pop_method)
                && exprs_are_same(cx, collection_expr, pop_collection)
            {
                let param_name = if let [param] = body.params
                    && let Some(ident) = param.pat.simple_ident()
                {
                    ident.name
                } else {
                    return None;
                };

                return Some(ManualPopIfPattern {
                    collection_expr,
                    predicate,
                    param_name,
                    if_span: if_expr_span,
                    collection_type,
                });
            }
        }

        None
    }

    fn is_collection_type(cx: &LateContext<'_>, expr: &Expr<'_>, collection_type: CollectionMethod) -> bool {
        let ty = cx.typeck_results().expr_ty(expr).peel_refs();
        match collection_type {
            CollectionMethod::VecPopIf => ty.is_diag_item(cx, sym::Vec),
            CollectionMethod::VecDequePopBackIf | CollectionMethod::VecDequePopFrontIf => {
                ty.is_diag_item(cx, sym::VecDeque)
            },
        }
    }

    fn check_pop_unwrap<'tcx>(expr: &'tcx Expr<'_>, pop_method: &str) -> Option<(&'tcx Expr<'tcx>, Span)> {
        let inner_expr = if let ExprKind::Block(block, _) = expr.kind
            && let [stmt] = block.stmts
            && let rustc_hir::StmtKind::Semi(e) | rustc_hir::StmtKind::Expr(e) = stmt.kind
        {
            e
        } else {
            expr
        };

        // Match collection.pop_method().unwrap()
        if let ExprKind::MethodCall(unwrap_path, receiver, _, _) = inner_expr.kind
            && unwrap_path.ident.name == sym::unwrap
            && let ExprKind::MethodCall(pop_path, collection_expr, _, _) = receiver.kind
            && pop_path.ident.as_str() == pop_method
        {
            return Some((collection_expr, inner_expr.span));
        }

        None
    }

    fn is_safe_to_replace(&self, pattern: &ManualPopIfPattern<'_>) -> bool {
        let has_closure = matches!(pattern.predicate.kind, ExprKind::Closure(_));
        let has_mutable_op = matches!(
            pattern.predicate.kind,
            ExprKind::Assign(..)
                | ExprKind::AssignOp(..)
                | ExprKind::AddrOf(rustc_hir::BorrowKind::Ref, rustc_hir::Mutability::Mut, _)
        );
        !(has_closure || has_mutable_op) && !pattern.predicate.can_have_side_effects()
    }

    fn emit_lint(&self, cx: &LateContext<'_>, pattern: &ManualPopIfPattern<'_>) {
        let collection_snippet = snippet(cx, pattern.collection_expr.span, "..");
        let predicate_snippet = snippet(cx, pattern.predicate.span, "..");
        let param_name = pattern.param_name;
        let pop_if_method = pattern.collection_type.pop_if_method();

        let suggestion = format!("{collection_snippet}.{pop_if_method}(|{param_name}| {predicate_snippet});");

        span_lint_and_sugg(
            cx,
            MANUAL_POP_IF,
            pattern.if_span,
            format!("manual implementation of {}", pattern.collection_type),
            "try",
            suggestion,
            Applicability::MachineApplicable,
        );
    }
}

fn exprs_are_same(cx: &LateContext<'_>, expr1: &Expr<'_>, expr2: &Expr<'_>) -> bool {
    SpanlessEq::new(cx).eq_expr(expr1, expr2)
}

impl<'tcx> LateLintPass<'tcx> for ManualPopIf {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'_>) {
        // Check if this is an `if` expression
        if let ExprKind::If(cond, then_block, None) = expr.kind {
            // Check if the popped value is used - if so, we can't replace with pop_if
            if Self::pop_value_is_used(then_block) {
                return;
            }

            // Try to match each pattern for each collection method
            for &collection_type in &[
                CollectionMethod::VecPopIf,
                CollectionMethod::VecDequePopBackIf,
                CollectionMethod::VecDequePopFrontIf,
            ] {
                // Check MSRV before attempting to match patterns
                if !self.msrv.meets(cx, collection_type.msrv()) {
                    continue;
                }

                // Try to match the is_some_and pattern
                if let Some(pattern) = self.check_is_some_and_pattern(cx, cond, then_block, expr.span, collection_type)
                    && self.is_safe_to_replace(&pattern)
                {
                    self.emit_lint(cx, &pattern);
                    return;
                }

                // Try to match the if-let pattern
                if let Some(pattern) = self.check_if_let_pattern(cx, cond, then_block, expr.span, collection_type)
                    && self.is_safe_to_replace(&pattern)
                {
                    self.emit_lint(cx, &pattern);
                    return;
                }

                // Try to match the map/unwrap_or pattern
                if let Some(pattern) =
                    self.check_map_unwrap_or_pattern(cx, cond, then_block, expr.span, collection_type)
                    && self.is_safe_to_replace(&pattern)
                {
                    self.emit_lint(cx, &pattern);
                    return;
                }
            }
        }
    }
}
