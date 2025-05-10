use core::alloc::Layout;
use crate::{Alloc, DefaultAlloc, AllocError};

#[test]
fn test_alloc_and_dealloc() {
	let allocator = DefaultAlloc;
	let layout = Layout::from_size_align(16, 8).unwrap();
	// Allocate
	let ptr = allocator.alloc(layout).expect("alloc failed");
	// Write and read
	unsafe {
		ptr.as_ptr().write_bytes(0xAB, layout.size());
		for i in 0..layout.size() {
			assert_eq!(*ptr.as_ptr().add(i), 0xAB);
		}
		allocator.dealloc(ptr, layout);
	}
}

#[test]
fn test_alloc_zeroed() {
	let allocator = DefaultAlloc;
	let layout = Layout::from_size_align(32, 8).unwrap();
	let ptr = allocator.alloc_zeroed(layout).expect("alloc_zeroed failed");
	unsafe {
		for i in 0..layout.size() {
			assert_eq!(*ptr.as_ptr().add(i), 0);
		}
		allocator.dealloc(ptr, layout);
	}
}

#[test]
fn test_alloc_filled_and_patterned() {
	let allocator = DefaultAlloc;
	let layout = Layout::from_size_align(8, 1).unwrap();
	// Filled
	let ptr_filled = allocator.alloc_filled(layout, 0x5A).unwrap();
	unsafe {
		for i in 0..layout.size() {
			assert_eq!(*ptr_filled.as_ptr().add(i), 0x5A);
		}
		allocator.dealloc(ptr_filled, layout);
	}

	// Patterned: pattern = i
	let ptr_pat = allocator.alloc_patterned(layout, |i| (i as u8) * 2).unwrap();
	unsafe {
		for i in 0..layout.size() {
			assert_eq!(*ptr_pat.as_ptr().add(i), (i as u8) * 2);
		}
		allocator.dealloc(ptr_pat, layout);
	}
}

#[test]
fn test_grow_and_variants() {
	let allocator = DefaultAlloc;
	let old = Layout::from_size_align(4, 1).unwrap();
	let new = Layout::from_size_align(8, 1).unwrap();
	// Prepare initial block with values 1,2,3,4
	let ptr = allocator.alloc(old).unwrap();
	unsafe {
		for i in 0..old.size() {
			*ptr.as_ptr().add(i) = (i + 1) as u8;
		}
	}
	// grow without pattern: new bytes undefined but old preserved
	let grown = unsafe { allocator.grow(ptr, old, new).unwrap() };
	unsafe {
		for i in 0..old.size() {
			assert_eq!(*grown.as_ptr().add(i), (i + 1) as u8);
		}
		allocator.dealloc(grown, new);
	}

	// grow_zeroed: new tail zeros
	let ptr2 = allocator.alloc(old).unwrap();
	unsafe { ptr2.as_ptr().write_bytes(0xFF, old.size()); }
	let gz = unsafe { allocator.grow_zeroed(ptr2, old, new).unwrap() };
	unsafe {
		for i in 0..old.size() {
			assert_eq!(*gz.as_ptr().add(i), 0xFF);
		}
		for i in old.size()..new.size() {
			assert_eq!(*gz.as_ptr().add(i), 0);
		}
		allocator.dealloc(gz, new);
	}

	// grow_filled
	let ptr3 = allocator.alloc(old).unwrap();
	unsafe { ptr3.as_ptr().write_bytes(0xAA, old.size()); }
	let gf = allocator.grow_filled(ptr3, old, new, 0xBB).unwrap();
	unsafe {
		for i in 0..old.size() {
			assert_eq!(*gf.as_ptr().add(i), 0xAA);
		}
		for i in old.size()..new.size() {
			assert_eq!(*gf.as_ptr().add(i), 0xBB);
		}
		allocator.dealloc(gf, new);
	}

	// grow_patterned
	let ptr4 = allocator.alloc(old).unwrap();
	unsafe { ptr4.as_ptr().write_bytes(0x00, old.size()); }
	let gp = unsafe { allocator.grow_patterned(ptr4, old, new, |i| (i as u8) + 1).unwrap() };
	unsafe {
		for i in 0..old.size() {
			assert_eq!(*gp.as_ptr().add(i), 0);
		}
		for i in old.size()..new.size() {
			assert_eq!(*gp.as_ptr().add(i), (i as u8) + 1);
		}
		allocator.dealloc(gp, new);
	}
}

#[test]
fn test_shrink_and_error_cases() {
	let allocator = DefaultAlloc;
	let old = Layout::from_size_align(8, 1).unwrap();
	let new = Layout::from_size_align(4, 1).unwrap();
	let ptr = allocator.alloc(old).unwrap();
	unsafe { ptr.as_ptr().write_bytes(0xCC, old.size()); }
	let shr = unsafe { allocator.shrink(ptr, old, new).unwrap() };
	unsafe {
		for i in 0..new.size() {
			assert_eq!(*shr.as_ptr().add(i), 0xCC);
		}
	}

	// Error: shrink to larger
	let err = unsafe { allocator.shrink(shr, new, old).unwrap_err() };
	assert_eq!(err, AllocError::ShrinkBiggerNewLayout(new.size(), old.size()));

	// Error: grow to smaller
	let err2 = unsafe { allocator.grow(shr, old, new).unwrap_err() };
	assert_eq!(err2, AllocError::GrowSmallerNewLayout(old.size(), new.size()));

	unsafe {
		allocator.dealloc(shr, new);
	}
}

#[test]
fn test_realloc_variants() {
	let allocator = DefaultAlloc;
	let old = Layout::from_size_align(4, 1).unwrap();
	let new = Layout::from_size_align(2, 1).unwrap();
	let ptr = allocator.alloc_filled(old, 0xDD).unwrap();
	// realloc shrink
	let rs = unsafe { allocator.realloc(ptr, old, new).unwrap() };
	unsafe {
		for i in 0..new.size() {
			assert_eq!(*rs.as_ptr().add(i), 0xDD);
		}
		allocator.dealloc(rs, new);
	}

	// realloc grow
	let ptr2 = allocator.alloc_zeroed(old).unwrap();
	let rg = unsafe { allocator.realloc_zeroed(ptr2, old, Layout::from_size_align(6,1).unwrap()).unwrap() };
	unsafe {
		for i in 0..old.size() {
			assert_eq!(*rg.as_ptr().add(i), 0);
		}
		for i in old.size()..6 {
			assert_eq!(*rg.as_ptr().add(i), 0);
		}
		allocator.dealloc(rg, Layout::from_size_align(6,1).unwrap());
	}
}
