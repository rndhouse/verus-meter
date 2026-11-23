//! Exercise the executable counter after erasing the synchronization proof.
use vstd::resource::semaphore::Semaphore;

#[test]
fn explicit_release_returns_only_its_own_slot() {
    let semaphore = Semaphore::new(2);
    let first = semaphore.acquire();
    let second = semaphore.try_acquire().unwrap();
    assert!(semaphore.try_acquire().is_none());
    drop(first);
    assert!(semaphore.try_acquire().is_none());
    second.release();

    std::thread::scope(|scope| {
        scope.spawn(|| semaphore.acquire().release()).join().unwrap();
    });
    let last = semaphore.try_acquire().unwrap();
    assert!(semaphore.try_acquire().is_none());
    last.release();
    assert!(Semaphore::new(0).try_acquire().is_none());
}
