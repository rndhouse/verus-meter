use super::support::exact_peak;
use crate::common::*;
use crate::verify_one_file;

// Each width is exercised at its exact allowance and one byte below it. This
// checks actual charges independently of mem_size's use in contract formulas.

fn integer_cases(typ: &str, bytes: u64) {
    let code = format!(
        r#"
        fn f(a: {typ}, b: {typ}) requires a == 2, b == 3,
            resources memory <= BUDGET,
        {{
            let mut sum = a + b;
            let difference = b - a;
            let product = a * b;
            sum += 1;
            sum -= 1;
            sum *= 2;
            assert(sum == 10 && difference == 1 && product == 6);
            assert(peak(memory) <= 5 * mem_size({typ}));
        }}
    "#
    );
    exact_peak(&format!("{typ}_arithmetic"), &code, 5 * bytes);

    let code = format!(
        r#"
        fn update(data: &mut [{typ}]) requires data.len() >= 1,
            ensures final(data)[0] == 7{typ},
            resources memory <= mem_size(data),
        {{ data[0] = 7{typ}; }}
        fn read(data: &[{typ}]) resources memory <= mem_size(data) {{ let _unused = (); }}
        fn f() resources memory <= BUDGET {{
            let mut data = [0{typ}; 3];
            update(&mut data);
            read(&data);
            assert(data[0] == 7{typ});
            assert(peak(memory) <= mem_size([{typ}; 3]) + mem_size(&[{typ}]));
        }}
    "#
    );
    exact_peak(&format!("{typ}_array_slice"), &code, 3 * bytes + 16);

    let code = format!(
        r#"
        fn helper(value: {typ})
            resources memory <= mem_size(value) + if value < 3{typ} {{ mem_size([{typ}; 2]) }} else {{ mem_size([{typ}; 4]) }},
        {{
            if value < 3{typ} {{ let data = [0{typ}; 2]; }}
            else {{ let data = [0{typ}; 4]; }}
        }}
        fn forward(value: {typ}) resources memory <= mem_size(value) + mem_peak(helper(value)) {{ helper(value); }}
        fn narrowed(value: {typ}) requires value == 2{typ},
            resources memory <= mem_size(value) + mem_peak(helper(2{typ})),
        {{ helper(value); }}
        fn f() resources memory <= BUDGET {{ forward(2{typ}); narrowed(2{typ}); }}
    "#
    );
    exact_peak(&format!("{typ}_conditional_calls"), &code, 4 * bytes);
}

macro_rules! integer_tests {
    ($($typ:ident => $bytes:literal),* $(,)?) => { $(
        #[test]
        fn $typ() { integer_cases(stringify!($typ), $bytes); }
    )* };
}
integer_tests! { u8 => 1, i8 => 1, u16 => 2, i16 => 2, u32 => 4, i32 => 4,
u64 => 8, i64 => 8, u128 => 16, i128 => 16, usize => 8, isize => 8 }

#[test]
fn signed_literals_and_negation() {
    for (typ, bytes, minimum) in [
        ("i8", 1, "-128"),
        ("i16", 2, "-32768"),
        ("i32", 4, "-2147483648"),
        ("i64", 8, "-9223372036854775808"),
        ("i128", 16, "-170141183460469231731687303715884105728"),
        ("isize", 8, "-9223372036854775808"),
    ] {
        let code = format!(
            r#"
            global size_of usize == 8;
            fn f(x: {typ}) requires x == -3{typ}, resources memory <= BUDGET {{
                let positive = -x;
                let minimum = {minimum}{typ};
                let negative = [-1{typ}, -2{typ}];
                assert(positive == 3{typ});
                assert(minimum < negative[0]);
                assert(peak(memory) <= 5 * mem_size({typ}));
            }}
        "#
        );
        exact_peak(&format!("{typ}_negative"), &code, 5 * bytes);
    }
}

test_verify_one_file! {
    #[test] negative_selector_queries_and_forwarding verus_code! {
        use vstd::prelude::*;
        fn helper(n: i16) resources memory <= mem_size(n) + if n < -1i16 { mem_size([i16; 2]) } else { mem_size([i16; 4]) } {
            if n < -1i16 { let scratch = [-1i16; 2]; }
            else { let scratch = [-1i16; 4]; }
        }
        fn forward(n: i16) resources memory <= mem_size(n) + mem_peak(helper(n)) { helper(n); }
        fn f() resources memory <= mem_peak(forward(-2i16)) {
            forward(-2i16);
            assert(peak(memory) <= 8);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] negative_selector_wrong_branch_rejected verus_code! {
        fn helper(n: i64) resources memory <= mem_size(n) + if n < -1i64 { 1 } else { 2 } {}
        fn f() resources memory <= mem_peak(helper(-2i64)) { helper(0i64); }
    } => Err(err) => assert_vir_error_msg(err, "peak 10 bytes exceeds budget 9 bytes")
}

test_verify_one_file! {
    #[test] signed_overflow_remains_a_proof_failure verus_code! {
        fn f(x: i8) resources memory <= 2 {
            let sum = x + 1i8; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] unsigned_overflow_remains_a_proof_failure verus_code! {
        fn f(x: u128) resources memory <= 32 {
            let sum = x + 1u128; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] negation_overflow_remains_a_proof_failure verus_code! {
        fn f(x: i8) resources memory <= 2 {
            let opposite = -x; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

#[test]
fn mixed_integer_struct_has_no_padding() {
    exact_peak(
        "mixed_integer_struct",
        r#"
        struct Record { small: u8, signed: i16, wide: u128, offset: isize }
        fn f() resources memory <= BUDGET {
            let record = Record { small: 1u8, signed: -2i16, wide: 3u128, offset: -4isize };
            assert(peak(memory) <= mem_size(Record));
        }
    "#,
        27,
    );
}

test_verify_one_file! {
    #[test] wide_array_size_overflow_rejected verus_code! {
        use vstd::prelude::*;
        global size_of usize == 8;
        fn f() resources memory <= mem_size([u128; 1152921504606846976]) {}
    } => Err(err) => assert_vir_error_msg(err, "array sizes exceeding u64")
}

test_verify_one_file! {
    #[test] casts_still_rejected verus_code! {
        fn f(x: u8) resources memory <= 100 { let y = x as u64; }
    } => Err(err) => assert_vir_error_msg(err, "does not support this executable expression")
}

test_verify_one_file! {
    #[test] mathematical_integer_storage_still_rejected verus_code! {
        fn f() resources memory <= mem_size(int) {}
    } => Err(err) => assert_vir_error_msg(err, "does not support this type")
}

#[test]
fn integer_example() {
    verify_one_file(
        "integer_example",
        include_str!("../../../../../examples/resource/memory/integers.rs").into(),
        &["--compile"],
    )
    .unwrap();
}

test_verify_one_file! {
    #[test] wide_selector_comparisons_keep_all_bits verus_code! {
        fn helper(n: u128)
            resources memory <= mem_size(n) + if n > 18446744073709551615u128 { 1 } else { 2 },
        {}
        fn f() resources memory <= mem_peak(helper(18446744073709551616u128)) {
            helper(18446744073709551616u128);
            assert(peak(memory) <= 17);
        }
    } => Ok(())
}
