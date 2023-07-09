use std::alloc::{Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use inline_array::InlineArray;

const N_THREADS: usize = 4;
const N_CLONES_PER_THREAD: usize = 16 * 1024 * 1024;

#[global_allocator]
static ALLOCATOR: Alloc = Alloc;

static ALLOCATED: AtomicUsize = AtomicUsize::new(0);
static FREED: AtomicUsize = AtomicUsize::new(0);
static RESIDENT: AtomicUsize = AtomicUsize::new(0);

fn allocated() -> usize {
    ALLOCATED.swap(0, Ordering::Relaxed)
}

fn freed() -> usize {
    FREED.swap(0, Ordering::Relaxed)
}

fn resident() -> usize {
    RESIDENT.load(Ordering::Relaxed)
}

#[derive(Default, Debug, Clone, Copy)]
struct Alloc;

unsafe impl std::alloc::GlobalAlloc for Alloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ret = System.alloc(layout);
        assert_ne!(ret, std::ptr::null_mut());
        ALLOCATED.fetch_add(layout.size(), Ordering::Relaxed);
        RESIDENT.fetch_add(layout.size(), Ordering::Relaxed);
        std::ptr::write_bytes(ret, 0xa1, layout.size());
        ret
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        std::ptr::write_bytes(ptr, 0xde, layout.size());
        FREED.fetch_add(layout.size(), Ordering::Relaxed);
        RESIDENT.fetch_sub(layout.size(), Ordering::Relaxed);
        System.dealloc(ptr, layout)
    }
}

fn main() {
    let mut threads = vec![];

    let ivec = InlineArray::from(&[0; 64]);

    let barrier = std::sync::Arc::new(std::sync::Barrier::new(N_THREADS));

    let before = Instant::now();

    for _ in 0..N_THREADS {
        let ivec = ivec.clone();
        let barrier = barrier.clone();
        let thread = std::thread::spawn(move || {
            let mut ivecs = Vec::with_capacity(N_CLONES_PER_THREAD);
            barrier.wait();

            let before = std::time::Instant::now();

            for _ in 0..N_CLONES_PER_THREAD {
                ivecs.push(ivec.clone());
            }

            let after_clones = std::time::Instant::now();

            drop(ivecs);
            drop(ivec);

            let drop_time = after_clones.elapsed();

            let clones_per_second =
                (N_CLONES_PER_THREAD as u128) / (after_clones - before).as_micros();
            let drops_per_second = (N_CLONES_PER_THREAD as u128) / drop_time.as_micros();

            println!(
                "{} million clones/s, {} million drops/s",
                clones_per_second, drops_per_second
            );
        });
        threads.push(thread);
    }

    for thread in threads.into_iter() {
        thread.join().unwrap();
    }

    dbg!(before.elapsed());

    dbg!(allocated());
    dbg!(freed());
    dbg!(resident());

    drop(ivec);
    println!("after drop:");
    dbg!(before.elapsed());

    dbg!(allocated());
    dbg!(freed());
    dbg!(resident());
}
