use crate::{BooleanExpression as B, Comparison as C, Expression as E, *};

#[test]
fn exact_large_arithmetic_and_native_boundaries() {
    const EXPRESSION: E =
        E::add(&E::constant(1024), &E::multiply(&E::constant(8), &E::parameter(0)));
    let value = evaluate(&EXPRESSION, &[u64::MAX.into()]).unwrap();
    assert_eq!(value.to_string(), "147573952589676413944");
    assert!(!value.fits_within(u64::MAX));
    assert_eq!(value.to_u64(), Err(NativeRangeError));
    let maximum = evaluate(&E::parameter(0), &[u64::MAX.into()]).unwrap();
    assert!(maximum.fits_within(u64::MAX));
    assert!(!maximum.fits_within(u64::MAX - 1));
    assert_eq!(maximum.to_u64(), Ok(u64::MAX));
    assert!(value > maximum);
    // An unbounded intermediate can still yield a small final answer.
    const ZERO: E = E::multiply(&E::multiply(&E::parameter(0), &E::parameter(0)), &E::constant(0));
    let zero = evaluate(&ZERO, &[u64::MAX.into()]).unwrap();
    assert_eq!(zero.to_u64(), Ok(0));
    assert!(zero.fits_within(0));
}

#[test]
fn converts_each_supported_unsigned_input_exactly() {
    for (input, expected) in [
        (Input::from(u8::MAX), u64::from(u8::MAX)),
        (Input::from(u16::MAX), u64::from(u16::MAX)),
        (Input::from(u32::MAX), u64::from(u32::MAX)),
        (Input::from(u64::MAX), u64::MAX),
        (Input::from(usize::MAX), usize::MAX as u64),
    ] {
        assert_eq!(evaluate(&E::parameter(0), &[input]).unwrap().to_u64(), Ok(expected));
    }
}

#[test]
fn branches_and_boolean_operators_are_lazy() {
    // Unselected branches contain missing arguments and must not cause errors.
    const SELECTED: E = E::conditional(
        &B::or(&B::constant(true), &B::parameter(1)),
        &E::constant(7),
        &E::parameter(1),
    );
    assert_eq!(evaluate(&SELECTED, &[]).unwrap().to_u64(), Ok(7));
    const OPPOSITE: E = E::conditional(
        &B::and(&B::constant(false), &B::parameter(1)),
        &E::parameter(1),
        &E::constant(9),
    );
    assert_eq!(evaluate(&OPPOSITE, &[]).unwrap().to_u64(), Ok(9));
    const COMPOSED: E = E::conditional(
        &B::and(
            &B::not(&B::and(&B::constant(false), &B::parameter(1))),
            &B::or(&B::constant(true), &B::parameter(1)),
        ),
        &E::constant(11),
        &E::parameter(1),
    );
    assert_eq!(evaluate(&COMPOSED, &[]).unwrap().to_u64(), Ok(11));
    const PARAMETER: E = E::conditional(&B::parameter(0), &E::constant(1), &E::constant(2));
    assert_eq!(evaluate(&PARAMETER, &[true.into()]).unwrap().to_u64(), Ok(1));
    assert_eq!(evaluate(&PARAMETER, &[false.into()]).unwrap().to_u64(), Ok(2));
    const MIXED: E = E::conditional(
        &B::parameter(0),
        &E::multiply(&E::parameter(1), &E::constant(2)),
        &E::constant(0),
    );
    assert_eq!(evaluate(&MIXED, &[true.into(), 9u32.into()]).unwrap().to_u64(), Ok(18));

    const AND: B = B::and(&B::parameter(0), &B::parameter(1));
    const OR: B = B::or(&B::parameter(0), &B::parameter(1));
    for (left, right, conjunction, disjunction) in [
        (false, false, false, false),
        (false, true, false, true),
        (true, false, false, true),
        (true, true, true, true),
    ] {
        let inputs = [left.into(), right.into()];
        assert_eq!(AND.boolean(&inputs), Ok(conjunction));
        assert_eq!(OR.boolean(&inputs), Ok(disjunction));
    }
}

#[test]
fn compares_mathematical_integers() {
    for (operation, expected) in [
        (C::Equal, [false, true, false]),
        (C::NotEqual, [true, false, true]),
        (C::Less, [true, false, false]),
        (C::LessEqual, [true, true, false]),
        (C::Greater, [false, false, true]),
        (C::GreaterEqual, [false, true, true]),
    ] {
        const PARAMETER: E = E::parameter(0);
        const TEN: E = E::constant(10);
        let predicate = B::compare(operation, &PARAMETER, &TEN);
        for (input, expected) in [9u64, 10, 11].into_iter().zip(expected) {
            assert_eq!(predicate.boolean(&[input.into()]), Ok(expected));
        }
    }
    const LARGE: E = E::conditional(
        &B::compare(C::Greater, &E::multiply(&E::parameter(0), &E::constant(2)), &E::parameter(0)),
        &E::constant(1),
        &E::constant(0),
    );
    assert_eq!(evaluate(&LARGE, &[u64::MAX.into()]).unwrap().to_u64(), Ok(1));
    const SIGNED: E = E::multiply(&E::signed_constant(-2), &E::signed_constant(-3));
    assert_eq!(evaluate(&SIGNED, &[]).unwrap().to_u64(), Ok(6));
}

#[test]
fn reports_argument_errors_and_negative_results() {
    assert_eq!(evaluate(&E::signed_constant(-1), &[]), Err(QueryError::NegativeResult));
    assert_eq!(evaluate(&E::parameter(0), &[]), Err(QueryError::MissingInput { index: 0 }));
    assert_eq!(
        evaluate(&E::parameter(0), &[false.into()]),
        Err(QueryError::InputType { index: 0 })
    );
    const EXPRESSION: E = E::conditional(&B::parameter(0), &E::constant(1), &E::constant(0));
    assert_eq!(evaluate(&EXPRESSION, &[0u8.into()]), Err(QueryError::InputType { index: 0 }));
}

#[test]
fn model_sizes_use_source_storage_instead_of_abi_padding() {
    assert_eq!(<Option<u64> as ValueSize>::BYTES, 9);
    assert_eq!(<Vec<u32> as ValueSize>::BYTES, 24);
    assert_eq!(<Box<[u32]> as ValueSize>::BYTES, 16);
    assert_eq!(<[u32; 3] as ValueSize>::BYTES, 12);
    assert_eq!(<&[u32] as ReferenceSize>::BYTES, 16);
    assert_eq!(<&mut [u32; 3] as ReferenceSize>::BYTES, 8);
}
