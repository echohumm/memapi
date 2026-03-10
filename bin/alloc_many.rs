use {
    memapi2::{helpers::ptr_max_align, prelude::*},
    std::{
        env,
        error::Error,
        io::{BufRead, Write, stdin, stdout}
    }
};

fn main() {
    let o = stdout();
    let i = stdin();

    let mut out = o.lock();
    let mut inp = i.lock();

    let auto = env::args().any(|a| a == "--auto" || a == "-a");

    let a = DefaultAlloc;

    let mut total_sizes_tried: u128 = 0;
    let mut total_alloc_attempts: u128 = 0;
    let mut total_successes: u128 = 0;
    let mut total_failures: u128 = 0;
    let mut total_bytes_allocated: u128 = 0;
    let mut max_success_size: usize = 0;
    let mut max_success_align: usize = 0;
    let mut max_success_size_align: usize = 0;
    let mut max_align_attempted: usize = 0;

    let mut size = 1;
    let mut align = 1;
    loop {
        total_sizes_tried += 1;

        let err: Box<dyn Error> = loop {
            if !auto {
                inp.read_line(&mut String::new()).unwrap();
                write!(out, "\x1b[1A\x1b[2K").unwrap();
                out.flush().unwrap();
            }

            // Track an allocation attempt for this size/align pair
            total_alloc_attempts += 1;
            if align > max_align_attempted {
                max_align_attempted = align;
            }

            let layout = match Layout::from_size_align(size, align) {
                Ok(layout) => layout,
                Err(e) => {
                    total_failures += 1;
                    break Box::new(e)
                }
            };

            write!(out, "created Layout(size={}, align={})", layout.size(), layout.align())
                .unwrap();

            let ptr = a.alloc(layout);
            match ptr {
                Ok(ptr) => {
                    total_successes += 1;
                    total_bytes_allocated += layout.size() as u128;
                    if layout.size() > max_success_size {
                        max_success_size = layout.size();
                        max_success_size_align = layout.align();
                    }
                    if layout.align() > max_success_align {
                        max_success_align = layout.align();
                    }

                    write!(out, "; allocated ptr={:p}", ptr).unwrap();
                    write!(out, "; aligned_to={}", ptr_max_align(ptr)).unwrap();
                    writeln!(out).unwrap();
                    out.flush().unwrap();

                    unsafe {
                        a.dealloc(ptr, layout);
                    }
                }
                Err(e) => {
                    total_failures += 1;
                    break Box::new(e)
                }
            }

            align *= 2
        };

        writeln!(out, "Layout({}, {}) failed with error: {}\n", size, align, err).unwrap();
        if align == 1 {
            // we failed on the first attempt, size is too large.
            break;
        }
        align = 1;
        size += 1;
    }

    // Final summary
    let success_rate = if total_alloc_attempts == 0 {
        0.0
    } else {
        (total_successes as f64) / (total_alloc_attempts as f64) * 100.0
    };

    writeln!(out, "=== Final stats ===").unwrap();
    writeln!(out, "sizes tried: {}", total_sizes_tried).unwrap();
    writeln!(out, "allocation attempts: {}", total_alloc_attempts).unwrap();
    writeln!(out, "successes: {}", total_successes).unwrap();
    writeln!(out, "failures: {}", total_failures).unwrap();
    writeln!(out, "success rate: {:.2}%", success_rate).unwrap();
    writeln!(out, "total bytes allocated (sum of successful sizes): {}", total_bytes_allocated).unwrap();
    writeln!(out, "largest successful size: {}", max_success_size).unwrap();
    writeln!(out, "largest successful size's largest align: {}", max_success_size_align).unwrap();
    writeln!(out, "largest successful alignment: {}", max_success_align).unwrap();
    writeln!(out, "largest alignment attempted: {}", max_align_attempted).unwrap();
    writeln!(out, "====================").unwrap();
}
