//! Runtime evaluation of retained resource expressions.
//!
//! This prototype uses checked `u64` arithmetic. Queries evaluate declared model
//! allowances; they do not check execution preconditions or physical RAM.

/// A query could not represent its result in the prototype's numeric range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Overflow;

/// Expression data emitted by the query macro, interpreted by [`evaluate`].
#[doc(hidden)]
pub enum Expression {
    /// A model-byte constant.
    Constant(u64),
    /// The query's single unsigned input.
    Parameter,
    /// Mathematical sum of two expressions.
    Add(&'static Expression, &'static Expression),
    /// Mathematical product of two expressions.
    Multiply(&'static Expression, &'static Expression),
}

/// Evaluate generated expression data without wrapping on overflow.
#[doc(hidden)]
pub fn evaluate(expression: &Expression, parameter: u64) -> Result<u64, Overflow> {
    match expression {
        Expression::Constant(value) => Ok(*value),
        Expression::Parameter => Ok(parameter),
        Expression::Add(left, right) => {
            evaluate(left, parameter)?.checked_add(evaluate(right, parameter)?).ok_or(Overflow)
        }
        Expression::Multiply(left, right) => {
            evaluate(left, parameter)?.checked_mul(evaluate(right, parameter)?).ok_or(Overflow)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Expression::*, *};

    #[test]
    fn evaluates_input_and_reports_overflow() {
        let bound = Add(&Constant(1024), &Multiply(&Constant(8), &Parameter));
        assert_eq!(evaluate(&bound, 100), Ok(1824));
        assert_eq!(evaluate(&bound, 0), Ok(1024));
        assert_eq!(evaluate(&bound, u64::MAX), Err(Overflow));
    }
}
