//! Memory contracts on callers of the verified vstd semaphore.
use super::*;

const SOURCE: &str = include_str!("semaphore.verus.rs");

#[test]
fn verified_permit_follows_its_input_across_a_conditional_return() {
    let trace =
        verify_one_file("metered_permit", SOURCE.into(), &["--trace", "--no-cheating"]).unwrap();
    for message in [
        "47-byte allocation observed with holder issued by input 0",
        "48-byte allocation observed with holder issued by input 1",
        "73-byte allocation only observed within intact holder input 0",
        "74-byte allocation also observed outside intact holder input 0",
        "dynamic storage region only observed within intact holder input 0",
    ] {
        assert!(
            trace.notes.iter().any(|note| note.message == message),
            "missing observation {expected}",
            expected = message
        );
    }
}

#[test]
fn imported_semaphore_operations_require_their_measured_workspace() {
    for (name, peak) in [("create", 40), ("attempt", 81), ("wait", 98), ("release", 72)] {
        let short = peak - 1;
        let source = SOURCE
            .replace(&format!("peak(memory) <= {peak},"), &format!("peak(memory) <= {short},"));
        let error = verify_one_file(&format!("short_permit_{name}"), source, &["--no-cheating"])
            .unwrap_err();
        assert_vir_error_msg(error, &format!("peak {peak} bytes exceeds budget {short} bytes"));
    }
}

#[test]
fn a_worker_can_retain_and_release_its_captured_permit() {
    let source = format!(
        "{SOURCE}\n{}",
        code_str! {
            verus! {
                fn worker(p: Permit<'static>, keep: bool)
                    resources peak(memory) <= 512,
                {
                    let task = move || {
                        if let Some(q) = retain(p, keep) {
                            let buffer = Box::new([0u8; 75]);
                            drop(buffer);
                            q.release();
                        }
                    };
                    let handle = vstd::thread::spawn(task);
                    let done = handle.join();
                }
            }
        }
    );
    let trace = verify_one_file("worker_retained_permit", source, &["--trace", "--no-cheating"])
        .unwrap_err();
    assert_eq!(trace.errors.len(), 1);
    assert!(trace.errors[0].message.contains("global lifetime and interference proofs"));
    assert!(trace.notes.iter().any(|n| {
        n.message.starts_with("75-byte allocation only observed within intact holder capture ")
    }));
}

#[test]
fn independent_acquisitions_use_the_actual_shared_backing() {
    let worker_pair = code_str! {
        verus! {
            fn pair(k: usize) requires k == 1, resources peak(memory) <= 2400, {
                let s = std::sync::Arc::new(Semaphore::new(k));
                let a = s.clone();
                let r = vstd::thread::spawn(move || {
                    let g = wait(&a);
                    let data = Box::new([0u8; 2000]);
                    drop(data); g.release();
                });
                let t = vstd::thread::spawn(move || {
                    if let Some(g) = s.try_acquire() {
                        let data = Box::new([0u8; 2001]);
                        drop(data);
                        g.release();
                    }
                });
                let first = r.join();
                let second = t.join();
            }
        }
    };
    let separate = worker_pair.replace("s.clone()", "std::sync::Arc::new(Semaphore::new(k))");
    let release_early = worker_pair.replace("drop(data); g.release();", "g.release(); drop(data);");
    let two = worker_pair.replace(
        "let data = Box::new([0u8; 2000]);",
        "let other = Box::new([0u8; 2000]); let data = Box::new([0u8; 2000]); drop(other);",
    );
    for (name, code, shared) in [
        ("shared", worker_pair.to_owned(), true),
        ("separate", separate, false),
        ("early_release", release_early, true),
        ("two_buffers", two, true),
    ] {
        let result = verify_one_file(
            &format!("semaphore_{name}"),
            format!("{SOURCE}\n{code}"),
            &["--trace", "--no-cheating"],
        );
        let trace = if name == "shared" {
            result.unwrap()
        } else {
            let failure = result.unwrap_err();
            assert!(failure.errors.iter().any(|e| e.message.contains("memory budget exceeded")));
            failure
        };
        if name == "early_release" {
            continue;
        }
        let backing = |bytes| {
            let prefix =
                format!("{bytes}-byte allocation observed with holder issued by shared backing ");
            trace
                .notes
                .iter()
                .find_map(|n| n.message.strip_prefix(&prefix))
                .expect("checked issuer")
        };
        assert_eq!(backing(2000) == backing(2001), shared);
    }
}

#[test]
fn a_counted_population_uses_the_smaller_of_workers_and_permits() {
    let family = include_str!("semaphore_population.verus.rs");
    verify_one_file("permit_population", family.into(), &["--no-cheating"]).unwrap();
    let short = family.replace("(if n <= k { n } else { k }) * b", "b");
    let on_failure = family.replace(
        "permit.release();\n            }",
        "permit.release(); } else {
            let outside = Vec::<u8>::with_capacity(b as usize); drop(outside);
        }",
    );
    for (name, program) in [("only_one_permit", short), ("scratch_on_failure", on_failure)] {
        assert_ne!(family, program);
        let error = verify_one_file(name, program, &["--no-cheating"]).unwrap_err();
        assert_any_vir_error_msg(error, "memory budget exceeded");
    }
}

#[test]
fn capacity_comes_from_the_checked_constructor_argument() {
    let constructor = code_str! {
        use vstd::resource::holder::BoundedInstance;
        verus! {
            fn make(workers: usize, slots: usize) -> (s: Semaphore)
                ensures s.holder_limit() == slots,
                resources peak(memory) <= 96,
            {
                Semaphore::new(slots)
            }
        }
    };
    let batch = include_str!("semaphore_population.verus.rs")
        .replace("Semaphore::new(k as usize)", "make(n as usize, k as usize)");
    let source = format!("{batch}\n{constructor}");
    verify_one_file("constructor_argument", source.clone(), &["--no-cheating"]).unwrap();
    // At n=4 and k=1 all four allocations can now coexist.
    let wrong = source
        .replace("ensures s.holder_limit()", "ensures slots == 0 ==> s.holder_limit()")
        .replace(
            "Semaphore::new(slots)",
            "if slots == 0 { Semaphore::new(0) } else { Semaphore::new(workers) }",
        );
    let err =
        verify_one_file("different_constructor_argument", wrong, &["--no-cheating"]).unwrap_err();
    assert_any_vir_error_msg(err, "memory budget exceeded");
}

#[test]
fn matching_an_instance_id_does_not_prove_the_reported_capacity() {
    let adapter = code_str! {
        use vstd::resource::holder::{BoundedInstance, ProtocolInstance, role_of};
        verus! {
            struct ReportedLimit { semaphore: &'static Semaphore, limit: usize }
            impl ProtocolInstance for ReportedLimit {
                closed spec fn protocol_id(&self) -> vstd::resource::Loc { self.semaphore.id() }
            }
            impl BoundedInstance for ReportedLimit {
                closed spec fn holder_limit(&self) -> nat { self.limit as nat }
            }
            impl ReportedLimit {
                fn new(semaphore: &'static Semaphore, limit: usize) -> (s: Self)
                    ensures s.holder_limit() == limit,
                    resources peak(memory) <= 128,
                { Self { semaphore, limit } }

                fn wait(&self) -> (p: Permit<'static>)
                    ensures role_of(p, self),
                    resources peak(memory) <= 192,
                { self.semaphore.acquire() }
            }

            fn worker(semaphore: &'static Semaphore) resources peak(memory) <= 2560, {
                // This adapter truthfully identifies the real semaphore. Its
                // independent reported limit can be zero even when acquisition succeeds.
                let view = std::sync::Arc::new(ReportedLimit::new(semaphore, 0));
                let job = std::thread::spawn(move || {
                    let permit = view.wait();
                    let buffer = Box::new([0u8; 2048]); drop(buffer);
                    permit.release();
                });
                let done = job.join();
            }
        }
    };
    let source = format!("{SOURCE}\n{adapter}");
    verify_one_file("issuer_without_capacity", source.clone(), &["--no-cheating"]).unwrap();
    let err = verify_one_file(
        "unrelated_zero_limit",
        source.replace("<= 2560", "<= 512"),
        &["--no-cheating"],
    )
    .unwrap_err();
    assert_any_vir_error_msg(err, "memory budget exceeded");
}

#[test]
fn a_fixed_workers_success_phase_is_unreachable_at_zero_capacity() {
    let worker = code_str! {
        verus! {
            fn empty() resources peak(memory) <= 512, {
                let semaphore = std::sync::Arc::new(Semaphore::new(0));
                let job = std::thread::spawn(move || {
                    if let Some(p) = semaphore.try_acquire() {
                        let scratch = Box::new([0u8; 2048]); drop(scratch);
                        p.release();
                    }
                });
                let done = job.join();
            }
        }
    };
    let source = format!("{SOURCE}\n{worker}");
    verify_one_file("zero_fixed_worker", source.clone(), &["--no-cheating"]).unwrap();
    let err = verify_one_file(
        "one_fixed_permit",
        source.replace("Semaphore::new(0)", "Semaphore::new(1)"),
        &["--no-cheating"],
    )
    .unwrap_err();
    assert_any_vir_error_msg(err, "memory budget exceeded");
}
