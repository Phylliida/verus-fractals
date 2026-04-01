///  WGSL codegen: RuntimeArithExpr → WgslExpr → WGSL string.
///
///  This module bridges the verified RuntimeArithExpr expression trees
///  (from gpu_codegen.rs / ArithLimb) to the WgslExpr emitter
///  (from verus-cutedsl-codegen).
///
///  The trust boundary is the `to_wgsl_expr` conversion (~20 lines),
///  which is a 1:1 structural mapping between isomorphic types.

use verus_cutedsl::arith_expr::RuntimeArithExpr;
use verus_cutedsl_codegen::{WgslExpr, CmpOp};

///  Convert RuntimeArithExpr to WgslExpr (1:1 structural mapping).
pub fn to_wgsl_expr(e: &RuntimeArithExpr) -> WgslExpr {
    match e {
        RuntimeArithExpr::Const(c) => WgslExpr::Const(*c),
        RuntimeArithExpr::Var(v) => WgslExpr::Var(*v),
        RuntimeArithExpr::Add(a, b) => WgslExpr::Add(
            Box::new(to_wgsl_expr(a)), Box::new(to_wgsl_expr(b))),
        RuntimeArithExpr::Sub(a, b) => WgslExpr::Sub(
            Box::new(to_wgsl_expr(a)), Box::new(to_wgsl_expr(b))),
        RuntimeArithExpr::Mul(a, b) => WgslExpr::Mul(
            Box::new(to_wgsl_expr(a)), Box::new(to_wgsl_expr(b))),
        RuntimeArithExpr::Div(a, b) => WgslExpr::Div(
            Box::new(to_wgsl_expr(a)), Box::new(to_wgsl_expr(b))),
        RuntimeArithExpr::Mod(a, b) => WgslExpr::Mod(
            Box::new(to_wgsl_expr(a)), Box::new(to_wgsl_expr(b))),
        RuntimeArithExpr::Index(arr, idx) => WgslExpr::Index(
            *arr, Box::new(to_wgsl_expr(idx))),
        RuntimeArithExpr::Shr(a, b) => WgslExpr::Shr(
            Box::new(to_wgsl_expr(a)), Box::new(to_wgsl_expr(b))),
        RuntimeArithExpr::Cmp(op, a, b) => {
            let wgsl_op = match op {
                verus_cutedsl::arith_expr::RuntimeCmpOp::Lt => CmpOp::Lt,
                verus_cutedsl::arith_expr::RuntimeCmpOp::Le => CmpOp::Le,
                verus_cutedsl::arith_expr::RuntimeCmpOp::Gt => CmpOp::Gt,
                verus_cutedsl::arith_expr::RuntimeCmpOp::Ge => CmpOp::Ge,
                verus_cutedsl::arith_expr::RuntimeCmpOp::Eq => CmpOp::Eq,
                verus_cutedsl::arith_expr::RuntimeCmpOp::Ne => CmpOp::Ne,
            };
            WgslExpr::Cmp(wgsl_op, Box::new(to_wgsl_expr(a)), Box::new(to_wgsl_expr(b)))
        }
        RuntimeArithExpr::Reduce(var, bound, body) => WgslExpr::Reduce(
            *var, Box::new(to_wgsl_expr(bound)), Box::new(to_wgsl_expr(body))),
    }
}

///  Convert a RuntimeArithExpr directly to a WGSL expression string.
pub fn expr_to_wgsl(e: &RuntimeArithExpr, var_names: &[&str]) -> String {
    to_wgsl_expr(e).emit(var_names, &[])
}

///  Convert a Vec of ArithLimb expressions to WGSL variable declarations.
///  Each limb becomes: `let limb_NAME_K: u32 = EXPR;`
pub fn limbs_to_wgsl(
    limb_exprs: &[RuntimeArithExpr],
    name: &str,
    var_names: &[&str],
) -> String {
    let mut out = String::new();
    for (k, expr) in limb_exprs.iter().enumerate() {
        let wgsl = expr_to_wgsl(expr, var_names);
        out.push_str(&format!("  let {name}_{k}: u32 = u32({wgsl});\n"));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_to_wgsl() {
        let e = RuntimeArithExpr::Const(42);
        assert_eq!(expr_to_wgsl(&e, &[]), "42u");
    }

    #[test]
    fn test_var_to_wgsl() {
        let e = RuntimeArithExpr::Var(0);
        assert_eq!(expr_to_wgsl(&e, &["x"]), "x");
    }

    #[test]
    fn test_add_to_wgsl() {
        let e = RuntimeArithExpr::Add(
            Box::new(RuntimeArithExpr::Var(0)),
            Box::new(RuntimeArithExpr::Var(1)));
        assert_eq!(expr_to_wgsl(&e, &["a", "b"]), "(a + b)");
    }

    #[test]
    fn test_mod_div_to_wgsl() {
        //  This is what Karatsuba carry extraction looks like
        let sum = RuntimeArithExpr::Add(
            Box::new(RuntimeArithExpr::Var(0)),
            Box::new(RuntimeArithExpr::Var(1)));
        let base = RuntimeArithExpr::Const(4_294_967_296);
        let digit = RuntimeArithExpr::Mod(
            Box::new(sum.clone()), Box::new(base.clone()));
        let carry = RuntimeArithExpr::Div(
            Box::new(sum), Box::new(base));
        assert_eq!(
            expr_to_wgsl(&digit, &["a", "b"]),
            "((a + b) % 4294967296u)");
        assert_eq!(
            expr_to_wgsl(&carry, &["a", "b"]),
            "((a + b) / 4294967296u)");
    }
}
