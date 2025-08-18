use {
    crate::{Alloc, DefaultAlloc, Layout, type_props::PtrProps},
    core::{
        fmt::{Display, Formatter, Result as FmtResult},
        mem::transmute,
        ptr::{self, NonNull},
        slice
    }
};

pub(crate) struct String {
    buf: NonNull<u8>,
    len: usize,
    cap: usize,
    alloc: DefaultAlloc
}

impl String {
    pub(crate) fn from_str(str: &str) -> String {
        // SAFETY: all refs are valid for layout(), alloc returns at least the size of the layout
        //  bytes
        unsafe {
            let alloc = DefaultAlloc;
            let buf = alloc.alloc(str.layout()).unwrap();

            ptr::copy_nonoverlapping(str.as_ptr(), buf.as_ptr(), str.len());

            String { buf, len: str.len(), cap: str.len(), alloc }
        }
    }

    pub(crate) fn as_str(&self) -> &str {
        // SAFETY: we know the bytes are valid UTF-8
        unsafe {
            #[allow(clippy::transmute_bytes_to_str)]
            transmute(slice::from_raw_parts(self.buf.as_ptr(), self.len))
        }
    }

    // #[cfg(feature = "alloc_ext")]
    // pub(crate) fn append_u8(mut self, mut n: u8) -> String {
    //     // get ASCII bytes for number
    //     let mut digits = [0_u8; 3];
    //     let mut dlen = 0_usize;
    //
    //     if n == 0 {
    //         digits[0] = b'0';
    //         dlen = 1;
    //     } else {
    //         while n != 0 {
    //             digits[dlen] = b'0' + (n % 10);
    //             n /= 10;
    //             dlen += 1;
    //         }
    //
    //         // for some reason my ide refuses to acknowledge that `digits[..dlen].reverse()` is a
    //         //  valid method call, so, UFCS here
    //         <[u8]>::reverse(&mut digits[..dlen]);
    //     }
    //
    //     let old_len = self.len;
    //     let new_len = old_len + dlen;
    //
    //     // SAFETY: we know that the layout of the string is at least the size of the old length
    //     //  and this is only used with very small strings, so the operations will never overflow
    //     unsafe {
    //         let new_buf = self
    //             .alloc
    //             .alloc(Layout::from_size_align_unchecked(new_len, 1))
    //             .expect("alloc failed");
    //
    //         ptr::copy_nonoverlapping(self.buf.as_ptr(), new_buf.as_ptr(), old_len);
    //         ptr::copy_nonoverlapping(digits.as_ptr(), new_buf.as_ptr().add(old_len), dlen);
    //
    //         let old_layout = Layout::from_size_align_unchecked(self.cap, 1);
    //         self.alloc.dealloc(self.buf, old_layout);
    //
    //         self.buf = new_buf;
    //         self.len = new_len;
    //         self.cap = new_len;
    //
    //         self
    //     }
    // }
}

impl Display for String {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult { <str as Display>::fmt(self.as_str(), f) }
}

impl Drop for String {
    fn drop(&mut self) {
        // SAFETY: the cap will be valid because we allocated it
        unsafe {
            self.alloc.dealloc(self.buf, Layout::from_size_align_unchecked(self.cap, 1));
        }
    }
}
