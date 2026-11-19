//! Recover exact scalar results from a verified helper interface when its body
//! does not yield a scalar template. Only an unconditional result equality
//! (or returns clause) fixes a value for every normal return.

use super::*;
use crate::resource::memory::loops::local;

pub(super) fn call_result(
    function: &Function,
    values: &HashMap<usize, Value>,
    traced: Value,
    site: &Span,
) -> Value {
    if !contracts::scalar(&function.x.outer_ret.x.typ)
        || !matches!(traced, Value::Unknown | Value::UnknownSize(_))
    {
        return traced;
    }
    let input = |value: &Expr| {
        let name = local(value)?;
        let index = function.x.params.iter().position(|param| {
            param.x.name == name
                && (contracts::scalar(&param.x.typ)
                    || matches!(&*param.x.typ, TypX::Decorate(TypDecoration::Ref, None, _)))
        })?;
        values.get(&index)
    };
    let result = &function.x.inner_ret.x.name;
    function
        .x
        .returns
        .iter()
        .chain(function.x.ensure.0.iter().filter_map(|post| {
            let ExprX::Binary(BinaryOp::Eq(_), left, right) = &post.x else { return None };
            if local(left).as_ref() == Some(result) {
                Some(right)
            } else if local(right).as_ref() == Some(result) {
                Some(left)
            } else {
                None
            }
        }))
        .find_map(|rhs| translate(rhs, &input).map(Value::Scalar))
        .unwrap_or_else(|| match traced {
            Value::Unknown => Value::UnknownSize(Arc::new(site.clone())),
            missing => missing,
        })
}

/// Translate only pure operations whose meaning is independent of callee
/// locals, and use the same argument observations as the ownership template.
fn translate<'a>(value: &Expr, input: &impl Fn(&Expr) -> Option<&'a Value>) -> Option<Expr> {
    let length = |arg: &Expr| match input(arg)? {
        Value::CollectionLength(length) => Some(length.clone()),
        _ => None,
    };
    let x = match &value.x {
        ExprX::Const(Constant::Int(_) | Constant::Bool(_)) => return Some(value.clone()),
        ExprX::Var(_) | ExprX::ReadPlace(..) => {
            let Value::Scalar(actual) = input(value)? else { return None };
            return Some(actual.clone());
        }
        ExprX::Unary(UnaryOp::Length(ArrayKind::Slice), arg) => return length(arg),
        ExprX::Block(stmts, Some(tail)) if stmts.is_empty() => return translate(tail, input),
        ExprX::Call { target: CallTarget::Fun(_, f, _, _, attrs), args, .. }
            if attrs.resource_intrinsic == Some(ResourceIntrinsic::SliceLen)
                || *f == crate::fun!(CrateId::Vstd => "slice"; "spec_slice_len") =>
        {
            return length(args.first()?);
        }
        ExprX::Unary(op @ (UnaryOp::Not | UnaryOp::Clip { .. }), arg) => {
            ExprX::Unary(*op, translate(arg, input)?)
        }
        ExprX::Binary(
            op @ (BinaryOp::Eq(_) | BinaryOp::Ne | BinaryOp::Inequality(_) | BinaryOp::Arith(_)),
            a,
            b,
        ) => ExprX::Binary(*op, translate(a, input)?, translate(b, input)?),
        ExprX::Logical(op, a, b) => ExprX::Logical(*op, translate(a, input)?, translate(b, input)?),
        ExprX::If(cond, a, Some(b)) => {
            ExprX::If(translate(cond, input)?, translate(a, input)?, Some(translate(b, input)?))
        }
        _ => return None,
    };
    Some(value.new_x(x))
}
