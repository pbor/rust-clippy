use clippy_config::Conf;
use clippy_utils::diagnostics::span_lint_and_sugg;
use clippy_utils::msrvs::{self, Msrv};
use clippy_utils::res::MaybeDef;
use clippy_utils::source::{indent_of, reindent_multiline, snippet_with_context};
use clippy_utils::visitors::is_local_used;
use clippy_utils::{eq_expr_value, is_else_clause, is_lang_item_or_ctor, sym};
use rustc_ast::LitKind;
use rustc_errors::Applicability;
use rustc_hir::{Expr, ExprKind, LangItem, PatKind, RustcVersion, StmtKind};
use rustc_lint::{LateContext, LateLintPass};
use rustc_session::impl_lint_pass;
use rustc_span::{Span, Symbol};
use std::fmt;

declare_clippy_lint! {
    /// ### What it does
    /// Checks for code to be replaced by `pop_if` methods.
    ///
    /// ### Why is this bad?
    /// Using `pop_if` is more concise and idiomatic.
    ///
    /// ### Known issues
    /// The lint handles the case where the popped value is
    /// not used and the case where it is bound to a variable
    /// as the very first statement within the `if`. It does
    /// not handle more complex cases, for instance if the
    /// value is popped directly within an expression without
    /// a let binding.
    ///
    /// The lint also does not handle the case where the
    /// `if` condition is part of an `else if` branch.
    ///
    /// ### Examples
    /// ```no_run
    /// # use std::collections::VecDeque;
    /// # let mut vec = vec![1, 2, 3, 4, 5];
    /// # let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3, 4, 5]);
    /// if vec.last().is_some_and(|x| *x > 5) {
    ///     let value = vec.pop().unwrap();
    ///     println!("Popped: {value}");
    /// }
    /// if deque.back().is_some_and(|x| *x > 5) {
    ///     let value = deque.pop_back().unwrap();
    ///     println!("Popped: {value}");
    /// }
    /// if deque.front().is_some_and(|x| *x > 5) {
    ///     let value = deque.pop_front().unwrap();
    ///     println!("Popped: {value}");
    /// }
    /// ```
    /// Use instead:
    /// ```no_run
    /// # use std::collections::VecDeque;
    /// # let mut vec = vec![1, 2, 3, 4, 5];
    /// # let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3, 4, 5]);
    /// if let Some(value) = vec.pop_if(|x| *x > 5) {
    ///     println!("Popped: {value}");
    /// };
    /// if let Some(value) = deque.pop_back_if(|x| *x > 5) {
    ///     println!("Popped: {value}");
    /// };
    /// if let Some(value) = deque.pop_front_if(|x| *x > 5) {
    ///     println!("Popped: {value}");
    /// };
    /// ```
    #[clippy::version = "1.95.0"]
    pub MANUAL_POP_IF,
    complexity,
    "manual implementation of `pop_if` methods"
}

impl_lint_pass!(ManualPopIf => [MANUAL_POP_IF]);

pub struct ManualPopIf {
    msrv: Msrv,
}

impl ManualPopIf {
    pub fn new(conf: &'static Conf) -> Self {
        Self { msrv: conf.msrv }
    }
}

#[allow(clippy::enum_variant_names)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ManualPopIfKind {
    Vec,
    VecDequeBack,
    VecDequeFront,
}

impl ManualPopIfKind {
    fn check_method(self) -> Symbol {
        match self {
            ManualPopIfKind::Vec => sym::last,
            ManualPopIfKind::VecDequeBack => sym::back,
            ManualPopIfKind::VecDequeFront => sym::front,
        }
    }

    fn pop_method(self) -> Symbol {
        match self {
            ManualPopIfKind::Vec => sym::pop,
            ManualPopIfKind::VecDequeBack => sym::pop_back,
            ManualPopIfKind::VecDequeFront => sym::pop_front,
        }
    }

    fn pop_if_method(self) -> Symbol {
        match self {
            ManualPopIfKind::Vec => sym::pop_if,
            ManualPopIfKind::VecDequeBack => sym::pop_back_if,
            ManualPopIfKind::VecDequeFront => sym::pop_front_if,
        }
    }

    fn is_diag_item(self, cx: &LateContext<'_>, expr: &Expr<'_>) -> bool {
        let ty = cx.typeck_results().expr_ty(expr).peel_refs();
        match self {
            ManualPopIfKind::Vec => ty.is_diag_item(cx, sym::Vec),
            ManualPopIfKind::VecDequeBack | ManualPopIfKind::VecDequeFront => ty.is_diag_item(cx, sym::VecDeque),
        }
    }

    fn msrv(self) -> RustcVersion {
        match self {
            ManualPopIfKind::Vec => msrvs::VEC_POP_IF,
            ManualPopIfKind::VecDequeBack => msrvs::VEC_DEQUE_POP_BACK_IF,
            ManualPopIfKind::VecDequeFront => msrvs::VEC_DEQUE_POP_FRONT_IF,
        }
    }
}

impl fmt::Display for ManualPopIfKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ManualPopIfKind::Vec => write!(f, "`Vec::pop_if`"),
            ManualPopIfKind::VecDequeBack => write!(f, "`VecDeque::pop_back_if`"),
            ManualPopIfKind::VecDequeFront => write!(f, "`VecDeque::pop_front_if`"),
        }
    }
}

struct ManualPopIfPattern<'tcx> {
    kind: ManualPopIfKind,

    /// The collection (`vec` in `vec.last()`)
    collection_expr: &'tcx Expr<'tcx>,

    /// The closure (`*x > 5` in `|x| *x > 5`)
    predicate: &'tcx Expr<'tcx>,

    /// Parameter name for the closure (`x` in `|x| *x > 5`)
    param_name: Symbol,

    /// Span of the if expression (including the `if` keyword)
    if_span: Span,

    /// The variable name if the pop value is bound to a variable
    let_binding_name: Option<Symbol>,

    /// The then block expression
    then_block: &'tcx Expr<'tcx>,
}

impl ManualPopIfPattern<'_> {
    fn emit_lint(&self, cx: &LateContext<'_>) {
        let mut app = Applicability::MachineApplicable;
        let ctxt = self.if_span.ctxt();
        let collection_snippet = snippet_with_context(cx, self.collection_expr.span, ctxt, "..", &mut app).0;
        let predicate_snippet = snippet_with_context(cx, self.predicate.span, ctxt, "..", &mut app).0;
        let param_name = self.param_name;
        let pop_if_method = self.kind.pop_if_method();

        let suggestion = if self.let_binding_name.is_some() {
            let body = self.build_if_let_body(cx, ctxt, &mut app);
            format!(
                "if let Some({param_name}) = {collection_snippet}.{pop_if_method}(|{param_name}| {predicate_snippet}) {body}"
            )
        } else {
            format!("{collection_snippet}.{pop_if_method}(|{param_name}| {predicate_snippet});")
        };

        span_lint_and_sugg(
            cx,
            MANUAL_POP_IF,
            self.if_span,
            format!("manual implementation of {}", self.kind),
            "try",
            suggestion,
            app,
        );
    }

    fn build_if_let_body(
        &self,
        cx: &LateContext<'_>,
        ctxt: rustc_span::SyntaxContext,
        app: &mut Applicability,
    ) -> String {
        let ExprKind::Block(block, _) = self.then_block.kind else {
            return String::new();
        };

        let param_name = self.param_name.to_string();
        let let_binding_name = self.let_binding_name.map(|s| s.to_string());

        let mut transformed_stmts = Vec::new();

        // Skip the first statement, which is the let binding with pop
        for stmt in block.stmts.iter().skip(1) {
            let stmt_snippet = snippet_with_context(cx, stmt.span, ctxt, "..", app).0;
            let transformed = if let Some(ref var_name) = let_binding_name {
                stmt_snippet.replace(var_name, &param_name)
            } else {
                stmt_snippet.to_string()
            };
            transformed_stmts.push(transformed);
        }

        if let Some(expr) = block.expr {
            let expr_snippet = snippet_with_context(cx, expr.span, ctxt, "..", app).0;
            let transformed = if let Some(ref var_name) = let_binding_name {
                expr_snippet.replace(var_name, &param_name)
            } else {
                expr_snippet.to_string()
            };
            transformed_stmts.push(transformed);
        }

        if transformed_stmts.is_empty() {
            " {}".to_string()
        } else {
            let body = transformed_stmts.join("\n");
            let base_indent = indent_of(cx, self.if_span).unwrap_or(0);
            let block_indent = base_indent + 4;
            let reindented_body = reindent_multiline(&body, false, Some(block_indent));
            format!(" {{\n{}\n{}}}", reindented_body, " ".repeat(base_indent))
        }
    }
}

/// Checks for `collection.<pop_method>().unwrap()` or `collection.<pop_method>().expect(..)`
/// as the first statement in the block. Returns the collection expression and optionally
/// the variable name if the pop is in a let binding.
///
/// Matches if the pop is either:
/// 1. The only statement (not embedded in a macro or other expression)
/// 2. A let binding as the first statement
fn check_pop_unwrap<'tcx>(expr: &'tcx Expr<'_>, pop_method: Symbol) -> Option<(&'tcx Expr<'tcx>, Option<Symbol>)> {
    let ExprKind::Block(block, _) = expr.kind else {
        return None;
    };

    let first_stmt = block.stmts.first()?;

    // Check if the first statement is a let binding with pop call
    if let StmtKind::Let(local) = &first_stmt.kind
        && let Some(init) = local.init
        && let ExprKind::MethodCall(unwrap_path, receiver, _, _) = init.kind
        && matches!(unwrap_path.ident.name, sym::unwrap | sym::expect)
        && let ExprKind::MethodCall(pop_path, collection_expr, [], _) = receiver.kind
        && pop_path.ident.name == pop_method
    {
        let let_binding_name = if let PatKind::Binding(_, _, ident, _) = local.pat.kind {
            Some(ident.name)
        } else {
            None
        };
        return Some((collection_expr, let_binding_name));
    }

    // Check for single statement with the pop call (not in a macro or other expression)
    if let [_] = block.stmts
        && block.expr.is_none()
        && let StmtKind::Semi(stmt_expr) | StmtKind::Expr(stmt_expr) = &first_stmt.kind
        && let ExprKind::MethodCall(unwrap_path, receiver, _, _) = stmt_expr.kind
        && matches!(unwrap_path.ident.name, sym::unwrap | sym::expect)
        && let ExprKind::MethodCall(pop_path, collection_expr, [], _) = receiver.kind
        && pop_path.ident.name == pop_method
        && !stmt_expr.span.from_expansion()
    {
        return Some((collection_expr, None));
    }

    None
}

/// Checks for the pattern:
/// ```ignore
/// if vec.last().is_some_and(|x| *x > 5) {
///     vec.pop().unwrap();
/// }
/// ```
fn check_is_some_and_pattern<'tcx>(
    cx: &LateContext<'tcx>,
    cond: &'tcx Expr<'_>,
    then_block: &'tcx Expr<'_>,
    if_expr_span: Span,
    kind: ManualPopIfKind,
) -> Option<ManualPopIfPattern<'tcx>> {
    let check_method = kind.check_method();
    let pop_method = kind.pop_method();

    if let ExprKind::MethodCall(path, receiver, [closure_arg], _) = cond.kind
        && path.ident.name == sym::is_some_and
        && let ExprKind::MethodCall(check_path, collection_expr, [], _) = receiver.kind
        && check_path.ident.name == check_method
        && kind.is_diag_item(cx, collection_expr)
        && let ExprKind::Closure(closure) = closure_arg.kind
        && let body = cx.tcx.hir_body(closure.body)
        && let Some((pop_collection, let_binding_name)) = check_pop_unwrap(then_block, pop_method)
        && eq_expr_value(cx, collection_expr, pop_collection)
        && let Some(param) = body.params.first()
        && let Some(ident) = param.pat.simple_ident()
    {
        return Some(ManualPopIfPattern {
            kind,
            collection_expr,
            predicate: body.value,
            param_name: ident.name,
            if_span: if_expr_span,
            let_binding_name,
            then_block,
        });
    }

    None
}

/// Checks for the pattern:
/// ```ignore
/// if let Some(x) = vec.last() {
///     if *x > 5 {
///         vec.pop().unwrap();
///     }
/// }
/// ```
fn check_if_let_pattern<'tcx>(
    cx: &LateContext<'tcx>,
    cond: &'tcx Expr<'_>,
    then_block: &'tcx Expr<'_>,
    if_expr_span: Span,
    kind: ManualPopIfKind,
) -> Option<ManualPopIfPattern<'tcx>> {
    let check_method = kind.check_method();
    let pop_method = kind.pop_method();

    if let ExprKind::Let(let_expr) = cond.kind
        && let PatKind::TupleStruct(qpath, [binding_pat], _) = let_expr.pat.kind
    {
        let res = cx.qpath_res(&qpath, let_expr.pat.hir_id);

        if let Some(def_id) = res.opt_def_id()
            && is_lang_item_or_ctor(cx, def_id, LangItem::OptionSome)
            && let PatKind::Binding(_, binding_id, binding_name, _) = binding_pat.kind
            && let ExprKind::MethodCall(path, collection_expr, [], _) = let_expr.init.kind
            && path.ident.name == check_method
            && kind.is_diag_item(cx, collection_expr)
            && let ExprKind::Block(block, _) = then_block.kind
        {
            // The inner if can be either a statement or a block expression
            let inner_if = match (block.stmts, block.expr) {
                ([stmt], _) => match stmt.kind {
                    StmtKind::Expr(expr) | StmtKind::Semi(expr) => expr,
                    _ => return None,
                },
                ([], Some(expr)) => expr,
                _ => return None,
            };

            if let ExprKind::If(inner_cond, inner_then, None) = inner_if.kind
                && is_local_used(cx, inner_cond, binding_id)
                && let Some((pop_collection, let_binding_name)) = check_pop_unwrap(inner_then, pop_method)
                && eq_expr_value(cx, collection_expr, pop_collection)
            {
                return Some(ManualPopIfPattern {
                    kind,
                    collection_expr,
                    predicate: inner_cond,
                    param_name: binding_name.name,
                    if_span: if_expr_span,
                    let_binding_name,
                    then_block: inner_then,
                });
            }
        }
    }

    None
}

/// Checks for the pattern:
/// ```ignore
/// if let Some(x) = vec.last() && *x > 5 {
///     vec.pop().unwrap();
/// }
/// ```
fn check_let_chain_pattern<'tcx>(
    cx: &LateContext<'tcx>,
    cond: &'tcx Expr<'_>,
    then_block: &'tcx Expr<'_>,
    if_expr_span: Span,
    kind: ManualPopIfKind,
) -> Option<ManualPopIfPattern<'tcx>> {
    let check_method = kind.check_method();
    let pop_method = kind.pop_method();

    if let ExprKind::Binary(op, left, right) = cond.kind
        && op.node == rustc_ast::BinOpKind::And
        && let ExprKind::Let(let_expr) = left.kind
        && let PatKind::TupleStruct(qpath, [binding_pat], _) = let_expr.pat.kind
    {
        let res = cx.qpath_res(&qpath, let_expr.pat.hir_id);

        if let Some(def_id) = res.opt_def_id()
            && is_lang_item_or_ctor(cx, def_id, LangItem::OptionSome)
            && let PatKind::Binding(_, binding_id, binding_name, _) = binding_pat.kind
            && let ExprKind::MethodCall(path, collection_expr, [], _) = let_expr.init.kind
            && path.ident.name == check_method
            && kind.is_diag_item(cx, collection_expr)
            && is_local_used(cx, right, binding_id)
            && let Some((pop_collection, let_binding_name)) = check_pop_unwrap(then_block, pop_method)
            && eq_expr_value(cx, collection_expr, pop_collection)
        {
            return Some(ManualPopIfPattern {
                kind,
                collection_expr,
                predicate: right,
                param_name: binding_name.name,
                if_span: if_expr_span,
                let_binding_name,
                then_block,
            });
        }
    }

    None
}

/// Checks for the pattern:
/// ```ignore
/// if vec.last().map(|x| *x > 5).unwrap_or(false) {
///     vec.pop().unwrap();
/// }
/// ```
fn check_map_unwrap_or_pattern<'tcx>(
    cx: &LateContext<'tcx>,
    cond: &'tcx Expr<'_>,
    then_block: &'tcx Expr<'_>,
    if_expr_span: Span,
    kind: ManualPopIfKind,
) -> Option<ManualPopIfPattern<'tcx>> {
    let check_method = kind.check_method();
    let pop_method = kind.pop_method();

    if let ExprKind::MethodCall(unwrap_path, receiver, [default_arg], _) = cond.kind
        && unwrap_path.ident.name == sym::unwrap_or
        && matches!(default_arg.kind, ExprKind::Lit(lit) if matches!(lit.node, LitKind::Bool(false)))
        && let ExprKind::MethodCall(map_path, map_receiver, [closure_arg], _) = receiver.kind
        && map_path.ident.name == sym::map
        && let ExprKind::MethodCall(check_path, collection_expr, [], _) = map_receiver.kind
        && check_path.ident.name == check_method
        && kind.is_diag_item(cx, collection_expr)
        && let ExprKind::Closure(closure) = closure_arg.kind
        && let body = cx.tcx.hir_body(closure.body)
        && cx.typeck_results().expr_ty(body.value).is_bool()
        && let Some((pop_collection, let_binding_name)) = check_pop_unwrap(then_block, pop_method)
        && eq_expr_value(cx, collection_expr, pop_collection)
        && let Some(param) = body.params.first()
        && let Some(ident) = param.pat.simple_ident()
    {
        return Some(ManualPopIfPattern {
            kind,
            collection_expr,
            predicate: body.value,
            param_name: ident.name,
            if_span: if_expr_span,
            let_binding_name,
            then_block,
        });
    }

    None
}

impl<'tcx> LateLintPass<'tcx> for ManualPopIf {
    fn check_expr(&mut self, cx: &LateContext<'tcx>, expr: &'tcx Expr<'_>) {
        let ExprKind::If(cond, then_block, None) = expr.kind else {
            return;
        };

        // Do not lint if we are in an else-if branch.
        if is_else_clause(cx.tcx, expr) {
            return;
        }

        for kind in [
            ManualPopIfKind::Vec,
            ManualPopIfKind::VecDequeBack,
            ManualPopIfKind::VecDequeFront,
        ] {
            if let Some(pattern) = check_is_some_and_pattern(cx, cond, then_block, expr.span, kind)
                .or_else(|| check_if_let_pattern(cx, cond, then_block, expr.span, kind))
                .or_else(|| check_let_chain_pattern(cx, cond, then_block, expr.span, kind))
                .or_else(|| check_map_unwrap_or_pattern(cx, cond, then_block, expr.span, kind))
                && self.msrv.meets(cx, kind.msrv())
            {
                pattern.emit_lint(cx);
                return;
            }
        }
    }
}
