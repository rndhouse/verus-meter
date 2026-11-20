//! Runtime evaluation of retained resource expressions using exact integers.
//!
//! Queries evaluate declared model allowances. Callers remain responsible for
//! execution preconditions; evaluating a query does not reserve physical memory.

mod expression;
mod layout;

#[doc(hidden)]
pub use layout::{ForLoopSize, ReferenceSize, ValueSize};

#[doc(hidden)]
pub use expression::{
    BindingExpression, BooleanExpression, Comparison, Expression, Input, Program, evaluate,
    evaluate_program,
};

use num_bigint::BigUint;
use num_traits::ToPrimitive;
use std::fmt;

/// A nonnegative memory allowance in bytes of the source-level memory model.
///
/// The value may exceed native integer ranges. Compare it directly with a budget
/// before requesting a native representation.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ModelBytes(BigUint);

impl ModelBytes {
    /// Whether this allowance is at most the supplied model-byte budget.
    ///
    /// ```
    /// # use verus_meter_runtime::{evaluate, Expression};
    /// # let required = evaluate(&Expression::constant(1124), &[]).unwrap();
    /// assert!(required.fits_within(1200));
    /// assert!(!required.fits_within(1000));
    /// assert_eq!(required.to_u64()?, 1124);
    /// # Ok::<(), verus_meter_runtime::NativeRangeError>(())
    /// ```
    pub fn fits_within(&self, budget: u64) -> bool {
        self.0 <= BigUint::from(budget)
    }

    /// Convert to a native integer, failing when the allowance exceeds `u64`.
    pub fn to_u64(&self) -> Result<u64, NativeRangeError> {
        self.0.to_u64().ok_or(NativeRangeError)
    }
}

impl fmt::Display for ModelBytes {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(formatter)
    }
}

/// An allowance cannot be represented by the requested native integer type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeRangeError;

impl fmt::Display for NativeRangeError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("model-byte allowance exceeds u64")
    }
}

impl std::error::Error for NativeRangeError {}

/// A retained expression could not produce a nonnegative byte allowance.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QueryError {
    /// A generated expression referred to an absent argument.
    MissingInput {
        /// Position in the query's argument list.
        index: usize,
    },
    /// An argument had a different type from the expression's parameter node.
    InputType {
        /// Position in the query's argument list.
        index: usize,
    },
    /// A retained binding has a forward/cyclic reference or the wrong scalar type.
    InvalidBinding {
        /// Position in the retained program's binding list.
        index: usize,
    },
    /// The resulting mathematical integer was negative.
    NegativeResult,
}

impl fmt::Display for QueryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingInput { index } => write!(formatter, "missing query argument {index}"),
            Self::InputType { index } => {
                write!(formatter, "incorrect type for query argument {index}")
            }
            Self::InvalidBinding { index } => {
                write!(formatter, "invalid retained query binding {index}")
            }
            Self::NegativeResult => formatter.write_str("memory allowance is negative"),
        }
    }
}

impl std::error::Error for QueryError {}
