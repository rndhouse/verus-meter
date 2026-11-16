//! Typed generated expression data. Constructors are public only for macro output;
//! private nodes prevent callers from mixing Boolean and integer operands.
use crate::{ModelBytes, QueryError};
use num_bigint::BigInt;

/// An exactly converted scalar argument supplied by a generated wrapper.
#[doc(hidden)]
pub struct Input(Value);

#[derive(Clone)]
enum Value {
    Integer(BigInt),
    Boolean(bool),
}

macro_rules! unsigned_inputs {
    ($($ty:ty),* $(,)?) => {
        $(impl From<$ty> for Input {
            fn from(value: $ty) -> Self {
                Self(Value::Integer(BigInt::from(value)))
            }
        })*
    };
}

unsigned_inputs!(u8, u16, u32, u64, usize);

impl From<bool> for Input {
    fn from(value: bool) -> Self {
        Self(Value::Boolean(value))
    }
}

/// A retained integer expression with statically typed operands.
#[doc(hidden)]
pub struct Expression(IntegerNode);

enum IntegerNode {
    Constant(u64),
    SignedConstant(i64),
    Parameter(usize),
    Binding(usize),
    Add(&'static Expression, &'static Expression),
    Multiply(&'static Expression, &'static Expression),
    If(&'static BooleanExpression, &'static Expression, &'static Expression),
}

impl Expression {
    /// Retain a nonnegative integer literal without a runtime allocation.
    pub const fn constant(value: u64) -> Self {
        Self(IntegerNode::Constant(value))
    }

    /// Retain a signed literal; only the final byte result must be nonnegative.
    pub const fn signed_constant(value: i64) -> Self {
        Self(IntegerNode::SignedConstant(value))
    }

    /// Refer to an integer input at its original argument position.
    pub const fn parameter(index: usize) -> Self {
        Self(IntegerNode::Parameter(index))
    }

    /// Refer to a shared integer binding in the retained program.
    pub const fn binding(index: usize) -> Self {
        Self(IntegerNode::Binding(index))
    }

    /// Retain a mathematical sum.
    pub const fn add(left: &'static Self, right: &'static Self) -> Self {
        Self(IntegerNode::Add(left, right))
    }

    /// Retain a mathematical product.
    pub const fn multiply(left: &'static Self, right: &'static Self) -> Self {
        Self(IntegerNode::Multiply(left, right))
    }

    /// Retain a conditional that evaluates only the selected integer branch.
    pub const fn conditional(
        condition: &'static BooleanExpression,
        then_value: &'static Self,
        else_value: &'static Self,
    ) -> Self {
        Self(IntegerNode::If(condition, then_value, else_value))
    }

    fn integer(&self, evaluator: &mut Evaluator<'_>) -> Result<BigInt, QueryError> {
        Ok(match &self.0 {
            IntegerNode::Constant(value) => BigInt::from(*value),
            IntegerNode::SignedConstant(value) => BigInt::from(*value),
            IntegerNode::Parameter(index) => match input(evaluator.inputs, *index)? {
                Value::Integer(value) => value.clone(),
                Value::Boolean(_) => return Err(QueryError::InputType { index: *index }),
            },
            IntegerNode::Binding(index) => match evaluator.binding(*index)? {
                Value::Integer(value) => value,
                Value::Boolean(_) => return Err(QueryError::InvalidBinding { index: *index }),
            },
            IntegerNode::Add(left, right) => left.integer(evaluator)? + right.integer(evaluator)?,
            IntegerNode::Multiply(left, right) => {
                left.integer(evaluator)? * right.integer(evaluator)?
            }
            IntegerNode::If(condition, then_value, else_value) => {
                if condition.boolean(evaluator)? {
                    then_value.integer(evaluator)?
                } else {
                    else_value.integer(evaluator)?
                }
            }
        })
    }
}

/// A mathematical integer comparison used in generated predicates.
#[doc(hidden)]
pub enum Comparison {
    /// Mathematical equality.
    Equal,
    /// Mathematical inequality.
    NotEqual,
    /// Strictly less than.
    Less,
    /// Less than or equal to.
    LessEqual,
    /// Strictly greater than.
    Greater,
    /// Greater than or equal to.
    GreaterEqual,
}

/// A retained Boolean expression with lazy logical operators.
#[doc(hidden)]
pub struct BooleanExpression(BooleanNode);

enum BooleanNode {
    Constant(bool),
    Parameter(usize),
    Binding(usize),
    Compare(Comparison, &'static Expression, &'static Expression),
    Not(&'static BooleanExpression),
    And(&'static BooleanExpression, &'static BooleanExpression),
    Or(&'static BooleanExpression, &'static BooleanExpression),
}

impl BooleanExpression {
    /// Retain a Boolean literal.
    pub const fn constant(value: bool) -> Self {
        Self(BooleanNode::Constant(value))
    }

    /// Refer to a Boolean input at its original argument position.
    pub const fn parameter(index: usize) -> Self {
        Self(BooleanNode::Parameter(index))
    }

    /// Refer to a shared Boolean binding in the retained program.
    pub const fn binding(index: usize) -> Self {
        Self(BooleanNode::Binding(index))
    }

    /// Retain a comparison of exact integers.
    pub const fn compare(
        operation: Comparison,
        left: &'static Expression,
        right: &'static Expression,
    ) -> Self {
        Self(BooleanNode::Compare(operation, left, right))
    }

    /// Retain logical negation.
    pub const fn not(value: &'static Self) -> Self {
        Self(BooleanNode::Not(value))
    }

    /// Retain conjunction, skipping the right operand when the left is false.
    pub const fn and(left: &'static Self, right: &'static Self) -> Self {
        Self(BooleanNode::And(left, right))
    }

    /// Retain disjunction, skipping the right operand when the left is true.
    pub const fn or(left: &'static Self, right: &'static Self) -> Self {
        Self(BooleanNode::Or(left, right))
    }

    fn boolean(&self, evaluator: &mut Evaluator<'_>) -> Result<bool, QueryError> {
        Ok(match &self.0 {
            BooleanNode::Constant(value) => *value,
            BooleanNode::Parameter(index) => match input(evaluator.inputs, *index)? {
                Value::Boolean(value) => *value,
                Value::Integer(_) => return Err(QueryError::InputType { index: *index }),
            },
            BooleanNode::Binding(index) => match evaluator.binding(*index)? {
                Value::Boolean(value) => value,
                Value::Integer(_) => return Err(QueryError::InvalidBinding { index: *index }),
            },
            BooleanNode::Compare(operation, left, right) => {
                let left = left.integer(evaluator)?;
                let right = right.integer(evaluator)?;
                match operation {
                    Comparison::Equal => left == right,
                    Comparison::NotEqual => left != right,
                    Comparison::Less => left < right,
                    Comparison::LessEqual => left <= right,
                    Comparison::Greater => left > right,
                    Comparison::GreaterEqual => left >= right,
                }
            }
            BooleanNode::Not(value) => !value.boolean(evaluator)?,
            BooleanNode::And(left, right) => {
                left.boolean(evaluator)? && right.boolean(evaluator)?
            }
            BooleanNode::Or(left, right) => left.boolean(evaluator)? || right.boolean(evaluator)?,
        })
    }
}

/// One shared scalar expression. Its references must point to earlier bindings.
#[doc(hidden)]
pub enum BindingExpression {
    /// A mathematical integer expression.
    Integer(Expression),
    /// A Boolean expression.
    Boolean(BooleanExpression),
}

/// Retained formula data with shared bindings, independent of runtime inputs.
#[doc(hidden)]
pub struct Program {
    expression: Expression,
    bindings: &'static [BindingExpression],
}

impl Program {
    /// Retain a root expression and bindings ordered after their dependencies.
    pub const fn new(expression: Expression, bindings: &'static [BindingExpression]) -> Self {
        Self { expression, bindings }
    }
}

/// Values are cached per query, keeping repeated uses linear in graph edges.
/// The active prefix enforces backward references, including on cache hits.
struct Evaluator<'a> {
    inputs: &'a [Input],
    bindings: &'a [BindingExpression],
    values: Vec<Option<Value>>,
    prefix: usize,
    #[cfg(test)]
    evaluated_bindings: usize,
}

impl<'a> Evaluator<'a> {
    fn new(inputs: &'a [Input], bindings: &'a [BindingExpression]) -> Self {
        Self {
            inputs,
            bindings,
            values: vec![None; bindings.len()],
            prefix: bindings.len(),
            #[cfg(test)]
            evaluated_bindings: 0,
        }
    }

    fn binding(&mut self, index: usize) -> Result<Value, QueryError> {
        if index >= self.prefix {
            return Err(QueryError::InvalidBinding { index });
        }
        if let Some(value) = &self.values[index] {
            return Ok(value.clone());
        }
        let bindings = self.bindings;
        let previous_prefix = self.prefix;
        self.prefix = index;
        #[cfg(test)]
        {
            self.evaluated_bindings += 1;
        }
        let result = match &bindings[index] {
            BindingExpression::Integer(value) => value.integer(self).map(Value::Integer),
            BindingExpression::Boolean(value) => value.boolean(self).map(Value::Boolean),
        };
        self.prefix = previous_prefix;
        let value = result?;
        self.values[index] = Some(value.clone());
        Ok(value)
    }
}

fn input(inputs: &[Input], index: usize) -> Result<&Value, QueryError> {
    inputs.get(index).map(|input| &input.0).ok_or(QueryError::MissingInput { index })
}

/// Interpret generated data, returning an exact nonnegative model-byte result.
///
/// Traversal uses stack space proportional to expression depth. Integer storage
/// grows with operand size; allocation failures are not converted into query errors.
#[doc(hidden)]
pub fn evaluate(expression: &Expression, inputs: &[Input]) -> Result<ModelBytes, QueryError> {
    expression
        .integer(&mut Evaluator::new(inputs, &[]))?
        .to_biguint()
        .map(ModelBytes)
        .ok_or(QueryError::NegativeResult)
}

/// Evaluate each demanded binding once for these inputs. Unselected branches and
/// unused bindings are not evaluated; cached values never survive between queries.
#[doc(hidden)]
pub fn evaluate_program(program: &Program, inputs: &[Input]) -> Result<ModelBytes, QueryError> {
    program
        .expression
        .integer(&mut Evaluator::new(inputs, program.bindings))?
        .to_biguint()
        .map(ModelBytes)
        .ok_or(QueryError::NegativeResult)
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
