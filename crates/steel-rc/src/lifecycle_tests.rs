use super::*;
use std::sync::{mpsc, Arc, Barrier};
use std::time::Duration;

#[derive(Debug)]
struct Probe(Arc<AtomicUsize>);

impl Drop for Probe {
    fn drop(&mut self) {
        assert_eq!(self.0.fetch_add(1, Ordering::SeqCst), 0, "dropped twice");
    }
}

fn probe() -> (BiasedRc<Probe>, Arc<AtomicUsize>) {
    let drops = Arc::new(AtomicUsize::new(0));
    (BiasedRc::new(Probe(drops.clone())), drops)
}

fn spawn<T: Send + 'static>(
    wrapped: bool,
    f: impl FnOnce() -> T + Send + 'static,
) -> JoinHandle<T> {
    if wrapped {
        with_explicit_merge(f)
    } else {
        std::thread::spawn(f)
    }
}

#[test]
fn live_owner_drains_without_retiring_and_preserves_aliases() {
    let (value, drops) = probe();
    let alias = value.clone();
    std::thread::spawn(move || drop(alias)).join().unwrap();
    let pending = QueueHandle::take_pending();
    assert!(!pending.is_empty());
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    assert!(QUEUE.map.contains_key(&ThreadId::current_thread().unwrap()));
    let survivor = value.clone();
    drop(value);
    assert_eq!(pending.merge(), 1);
    assert_eq!(BiasedRc::strong_count(&survivor), 1);
    QueueHandle::finish_thread_merge();
    assert!(QUEUE.map.contains_key(&ThreadId::current_thread().unwrap()));
    let alias = survivor.clone();
    assert_eq!(BiasedRc::strong_count(&alias), 2);
    drop(survivor);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    drop(alias);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn queued_release_keeps_an_already_merged_allocation_alive() {
    let (mut value, drops) = probe();
    let alias = value.clone();
    std::thread::spawn(move || drop(alias)).join().unwrap();
    let pending = QueueHandle::take_pending();
    value.clone().merge();
    assert!(BiasedRc::get_mut(&mut value).is_none());
    drop(value);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    assert_eq!(pending.merge(), 1);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn releases_before_and_after_owner_exit_and_unwinding() {
    for wrapped in [false, true] {
        for unwind in [false, true] {
            for release_before_exit in [false, true] {
                let (send, receive) = mpsc::channel();
                let (finish, wait) = mpsc::channel();
                let owner = spawn(wrapped, move || {
                    let (value, drops) = probe();
                    send.send((value, drops)).unwrap();
                    wait.recv_timeout(Duration::from_secs(10)).unwrap();
                    if unwind {
                        panic!("test owner unwinding");
                    }
                });
                let (value, drops) = receive.recv_timeout(Duration::from_secs(10)).unwrap();
                if release_before_exit {
                    drop(value);
                    assert_eq!(drops.load(Ordering::SeqCst), 0);
                    finish.send(()).unwrap();
                    assert_eq!(owner.join().is_err(), unwind);
                } else {
                    finish.send(()).unwrap();
                    assert_eq!(owner.join().is_err(), unwind);
                    assert_eq!(drops.load(Ordering::SeqCst), 0);
                    drop(value);
                }
                assert_eq!(drops.load(Ordering::SeqCst), 1);
            }
        }
    }
}

#[test]
fn release_marked_before_retirement_is_merged_after_retirement() {
    for wrapped in [false, true] {
        let (marked, wait_marked) = mpsc::channel();
        let (publish, wait_publish) = mpsc::channel();
        let owner = spawn(wrapped, move || {
            let (value, drops) = probe();
            let releaser = std::thread::spawn(move || {
                let value = ManuallyDrop::new(value);
                assert!(value.get_box().decrement() == DecrementAction::Queue);
                marked.send(()).unwrap();
                wait_publish.recv_timeout(Duration::from_secs(10)).unwrap();
                QueueHandle::enqueue(&value);
            });
            wait_marked.recv_timeout(Duration::from_secs(10)).unwrap();
            (releaser, drops)
        });
        let (releaser, drops) = owner.join().unwrap();
        assert_eq!(
            drops.load(Ordering::SeqCst),
            0,
            "queued allocation was freed early"
        );
        publish.send(()).unwrap();
        releaser.join().unwrap();
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    }
}

#[test]
fn returned_aliases_survive_retirement_and_worker_identity_is_never_reused() {
    let mut previous = 0;
    for worker in 0..64 {
        let (mut aliases, drops, id) = spawn(worker % 2 == 0, || {
            let (value, drops) = probe();
            let aliases = vec![value.clone(), value.clone(), value];
            (aliases, drops, ThreadId::current_thread().unwrap())
        })
        .join()
        .unwrap();
        assert!(id.0.get() > previous);
        previous = id.0.get();
        assert!(!QUEUE.map.contains_key(&id));
        let survivor = aliases.pop().unwrap();
        drop(aliases);
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        assert_eq!(survivor.0.load(Ordering::SeqCst), 0);
        assert_eq!(BiasedRc::strong_count(&survivor), 1);
        let clone = survivor.clone();
        drop(survivor);
        assert_eq!(drops.load(Ordering::SeqCst), 0);
        drop(clone);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    }
}

#[test]
fn concurrent_releases_race_with_retirement() {
    for _ in 0..32 {
        let ready = Arc::new(Barrier::new(9));
        let owner = std::thread::spawn(move || {
            let (value, drops) = probe();
            let workers: Vec<_> = (0..8)
                .map(|_| {
                    let alias = value.clone();
                    let ready = ready.clone();
                    std::thread::spawn(move || {
                        ready.wait();
                        drop(alias);
                    })
                })
                .collect();
            drop(value);
            ready.wait();
            (workers, drops)
        });
        let (workers, drops) = owner.join().unwrap();
        for worker in workers {
            worker.join().unwrap();
        }
        assert_eq!(drops.load(Ordering::SeqCst), 1);
    }
}

#[test]
fn merged_unique_access_does_not_consume_the_reference() {
    let mut value = BiasedRc::new(42);
    let alias = value.clone();
    std::thread::spawn(move || drop(alias)).join().unwrap();
    assert_eq!(QueueHandle::run_explicit_merge(), 1);
    for expected in 42..45 {
        let inner = BiasedRc::get_mut(&mut value).unwrap();
        assert_eq!(*inner, expected);
        *inner += 1;
        assert_eq!(BiasedRc::strong_count(&value), 1);
    }
    assert_eq!(BiasedRc::try_unwrap(value).unwrap(), 45);
}

#[test]
fn pending_destructors_can_reenter_the_registry() {
    struct Reenter(Arc<AtomicUsize>);
    impl Drop for Reenter {
        fn drop(&mut self) {
            register_thread();
            QueueHandle::run_explicit_merge();
            QueueHandle::finish_thread_merge();
            let (nested, drops) = probe();
            drop(nested);
            assert_eq!(drops.load(Ordering::SeqCst), 1);
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    for retire in [false, true] {
        let owner = std::thread::spawn(move || {
            let calls = Arc::new(AtomicUsize::new(0));
            let values = vec![
                BiasedRc::new(Reenter(calls.clone())),
                BiasedRc::new(Reenter(calls.clone())),
            ];
            std::thread::spawn(move || drop(values)).join().unwrap();
            if !retire {
                assert_eq!(QueueHandle::run_explicit_merge(), 2);
                assert_eq!(calls.load(Ordering::SeqCst), 2);
            }
            calls
        });
        assert_eq!(owner.join().unwrap().load(Ordering::SeqCst), 2);
    }
}

#[test]
fn tls_destructors_use_shared_counting_after_owner_retirement() {
    struct LateDrop {
        sender: mpsc::Sender<(BiasedRc<Probe>, Arc<AtomicUsize>)>,
        value: Option<BiasedRc<Probe>>,
    }
    impl Drop for LateDrop {
        fn drop(&mut self) {
            assert!(ThreadId::current_thread().is_none());
            drop(self.value.take());
            self.sender.send(probe()).unwrap();
        }
    }
    thread_local! {
        static LATE: std::cell::RefCell<Option<LateDrop>> = const { std::cell::RefCell::new(None) };
    }
    let (sender, receiver) = mpsc::channel();
    let owner = std::thread::spawn(move || {
        // TLS destructors run in reverse initialization order.
        LATE.with(|late| {
            *late.borrow_mut() = Some(LateDrop {
                sender,
                value: None,
            })
        });
        let (value, drops) = probe();
        LATE.with(|late| late.borrow_mut().as_mut().unwrap().value = Some(value));
        drops
    });
    let old_drops = owner.join().unwrap();
    assert_eq!(old_drops.load(Ordering::SeqCst), 1);
    let (value, drops) = receiver.recv_timeout(Duration::from_secs(10)).unwrap();
    assert!(value.meta().shared.load(Ordering::Acquire).is_merged());
    assert_eq!(BiasedRc::strong_count(&value), 1);
    drop(value);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

struct Chain {
    next: Option<BiasedRc<Chain>>,
    drops: Arc<Vec<AtomicUsize>>,
    index: usize,
}

impl Drop for Chain {
    fn drop(&mut self) {
        assert_eq!(self.drops[self.index].fetch_add(1, Ordering::SeqCst), 0);
        drop(self.next.take());
    }
}

fn chain(depth: usize) -> (BiasedRc<Chain>, Arc<Vec<AtomicUsize>>) {
    let drops = Arc::new((0..depth).map(|_| AtomicUsize::new(0)).collect::<Vec<_>>());
    let mut next = None;
    for index in 0..depth {
        next = Some(BiasedRc::new(Chain {
            next,
            drops: drops.clone(),
            index,
        }));
    }
    (next.unwrap(), drops)
}

#[test]
fn retired_owner_releases_nested_values_iteratively() {
    let (value, drops) = std::thread::spawn(|| chain(100_000)).join().unwrap();
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || drop(value))
        .unwrap()
        .join()
        .unwrap();
    assert!(drops.iter().all(|count| count.load(Ordering::SeqCst) == 1));
}

#[test]
fn retired_owner_releases_nested_values_during_late_tls_destruction() {
    struct LateDrop(Option<BiasedRc<Chain>>);
    impl Drop for LateDrop {
        fn drop(&mut self) {
            assert!(ThreadId::current_thread().is_none());
            drop(self.0.take());
        }
    }
    thread_local! {
        static LATE: std::cell::RefCell<Option<LateDrop>> = const { std::cell::RefCell::new(None) };
    }

    let (value, drops) = std::thread::spawn(|| chain(100_000)).join().unwrap();
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(move || {
            LATE.with(|late| *late.borrow_mut() = Some(LateDrop(Some(value))));
            register_thread();
            // Initialize the retired drain after LATE so a TLS destructor would run too early.
            drop(std::thread::spawn(|| BiasedRc::new(())).join().unwrap());
        })
        .unwrap()
        .join()
        .unwrap();
    assert!(drops.iter().all(|count| count.load(Ordering::SeqCst) == 1));
}

#[test]
fn retired_owner_drain_recovers_after_reentrant_destructor_panics() {
    struct PanicOnDrop(Vec<BiasedRc<Probe>>);
    impl Drop for PanicOnDrop {
        fn drop(&mut self) {
            register_thread();
            QueueHandle::run_explicit_merge();
            QueueHandle::finish_thread_merge();
            let drops: Vec<_> = self.0.iter().map(|probe| probe.0.clone()).collect();
            drop(mem::take(&mut self.0));
            assert!(drops.iter().all(|count| count.load(Ordering::SeqCst) == 0));
            panic!("test retired destructor unwinding");
        }
    }

    let (value, drops, recovery, recovery_drops) = std::thread::spawn(|| {
        let (first, first_drops) = probe();
        let (second, second_drops) = probe();
        let (recovery, recovery_drops) = probe();
        (
            BiasedRc::new(PanicOnDrop(vec![first, second])),
            [first_drops, second_drops],
            recovery,
            recovery_drops,
        )
    })
    .join()
    .unwrap();
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(value)));
    assert_eq!(
        panic.unwrap_err().downcast_ref::<&str>(),
        Some(&"test retired destructor unwinding")
    );
    assert!(drops.iter().all(|count| count.load(Ordering::SeqCst) == 1));
    drop(recovery);
    assert_eq!(recovery_drops.load(Ordering::SeqCst), 1);
}
