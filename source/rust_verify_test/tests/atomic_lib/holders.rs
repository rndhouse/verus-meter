use super::*;

test_verify_one_file! {
    #[test] a_forwarded_permit_retains_its_instance_in_a_worker code! {
        use vstd::prelude::*;
        use vstd::resource::holder::{Holder, BoundedHolder};
        use vstd::resource::semaphore::{Permit, Semaphore};
        use std::sync::Arc;

        verus! {
            fn forward<'a>(p: Permit<'a>, keep: bool) -> (result: Option<Permit<'a>>)
                ensures
                    result matches Some(q) ==> q.semaphore() == p.semaphore(),
                    result.is_some() == keep,
            {
                if keep { Some(p) } else { p.release(); None }
            }

            fn work(k: usize, retain: bool) {
                let s = Arc::new(Semaphore::new(k));
                let worker = vstd::thread::spawn(move || {
                    if let Some(p) = s.try_acquire() {
                        assert(k > 0 && p.instance_id() == s.id() && p.capacity() == k);
                        if let Some(q) = forward(p, retain) {
                            assert(q.instance_id() == s.id());
                            q.release();
                        }
                    }
                });
                let _ = worker.join();
                let zero = Semaphore::new(0);
                let empty = zero.try_acquire();
                assert(empty.is_none());
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] a_permit_does_not_justify_another_capacity code! {
        use vstd::prelude::*;
        use vstd::resource::semaphore::Semaphore;
        use vstd::resource::holder::BoundedHolder;
        verus! {
            fn wrong() {
                let a = Semaphore::new(2);
                let b = Semaphore::new(1);
                let p = a.acquire();
                assert(p.capacity() == b.capacity()); // FAILS
                p.release();
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] an_unrestricted_holder_cannot_prove_exclusion code! {
        use vstd::prelude::*;
        use vstd::resource::holder::{BoundedHolder, Holder};
        use vstd::resource::Loc;
        verus! {
            struct Fake { domain: Ghost<Loc> }
            impl Holder for Fake {
                closed spec fn instance_id(&self) -> Loc { self.domain@ }
            }
            impl BoundedHolder for Fake {
                open spec fn capacity(&self) -> nat { 1 }
                proof fn population_bound(tracked population: Seq<Self>, id: Loc, capacity: nat) {
                    assert(population.len() <= capacity); // FAILS
                }
            }
        }
    } => Err(e) => assert_one_fails(e)
}

#[test]
fn a_custom_exclusive_protocol_needs_the_successful_atomic_transition() {
    let source = include_str!("exclusive.verus.rs");
    verify_one_file("exclusive_holder", source.into(), &[]).unwrap();
    let broken = source.replace("if success.is_ok()", "if success.is_err()");
    let err = verify_one_file("failed_cas_holder", broken, &[]).unwrap_err();
    assert!(err.errors.iter().any(|d| d.message.contains("precondition not satisfied")));
}

test_verify_one_file! {
    #[test] write_and_read_handles_have_incompatible_roles code! {
        use vstd::prelude::*;
        use vstd::resource::holder::{Holder, BoundedHolder, Incompatible};
        use vstd::rwlock::{ReadHandle, RwLock, RwLockPredicate, WriteHandle};
        verus! {
            struct Any;
            impl RwLockPredicate<u8> for Any {
                open spec fn inv(self, _: u8) -> bool { true }
            }
            proof fn cannot_overlap(tracked mut writer: WriteHandle<'_, u8, Any>,
                                    tracked reader: ReadHandle<'_, u8, Any>)
                ensures writer.rwlock().id() != reader.rwlock().id(),
            {
                writer.distinct_instances(&reader);
            }
            fn two_readers() {
                let lock = RwLock::<u8, Any>::new(7, Ghost(Any));
                let first = lock.acquire_read();
                let second = lock.acquire_read();
                assert(first.instance_id() == second.instance_id());
                first.release_read();
                second.release_read();
                let (value, writer) = lock.acquire_write();
                assert(writer.instance_id() == lock.id() && writer.capacity() == 1);
                writer.release_write(value);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] equal_capacities_do_not_identify_two_semaphores code! {
        use vstd::prelude::*;
        use vstd::resource::holder::Holder;
        use vstd::resource::semaphore::Semaphore;
        verus! {
            fn wrong() {
                let a = Semaphore::new(1);
                let b = Semaphore::new(1);
                let p = a.acquire();
                assert(p.instance_id() == b.id()); // FAILS
                p.release();
            }
        }
    } => Err(e) => assert_one_fails(e)
}
