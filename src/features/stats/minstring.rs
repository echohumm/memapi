use crate::{type_props::PtrProps, Alloc, DefaultAlloc, Layout};
use core::{
    fmt::{Display, Formatter, Result as FmtResult},
    mem::transmute,
    ptr::{self, NonNull},
    slice,
};

pub(crate) struct String {
    bytes: Vec,
}

impl String {
    pub(crate) fn from_str(str: &str) -> String {
        // SAFETY: all refs are valid for layout(), alloc returns at least the size of the layout
        //  bytes
        unsafe {
            let alloc = DefaultAlloc;
            let buf = alloc.alloc(str.layout()).unwrap();

            ptr::copy_nonoverlapping(str.as_ptr(), buf.as_ptr(), str.len());

            String {
                bytes: Vec {
                    buf,
                    len: str.len(),
                    cap: str.len(),
                    alloc,
                },
            }
        }
    }

    pub(crate) fn as_str(&self) -> &str {
        // SAFETY: we know the bytes are valid UTF-8
        unsafe {
            #[allow(clippy::transmute_bytes_to_str)]
            transmute(slice::from_raw_parts(
                self.bytes.buf.as_ptr(),
                self.bytes.len,
            ))
        }
    }

    #[cfg(feature = "alloc_ext")]
    pub(crate) fn append_u8(mut self, mut n: u8) -> String {
        // get ASCII bytes for number
        let mut digits = [0_u8; 3];
        let mut dlen = 0_usize;

        if n == 0 {
            digits[0] = b'0';
            dlen = 1;
        } else {
            while n != 0 {
                digits[dlen] = b'0' + (n % 10);
                n /= 10;
                dlen += 1;
            }
            // digits are reversed; fix that in-place
            digits[..dlen].reverse();
        }

        let old_len = self.bytes.len;
        let new_len = old_len + dlen;

        // SAFETY: we know that the layout of the string is at least the size of the old length
        //  and this is only used with very small strings, so the operations will never overflow
        unsafe {
            let new_buf = self
                .bytes
                .alloc
                .alloc(Layout::from_size_align_unchecked(new_len, 1))
                .expect("alloc failed");

            ptr::copy_nonoverlapping(self.bytes.buf.as_ptr(), new_buf.as_ptr(), old_len);
            ptr::copy_nonoverlapping(digits.as_ptr(), new_buf.as_ptr().add(old_len), dlen);

            let old_layout = Layout::from_size_align_unchecked(self.bytes.cap, 1);
            self.bytes.alloc.dealloc(self.bytes.buf, old_layout);

            self.bytes.buf = new_buf;
            self.bytes.len = new_len;
            self.bytes.cap = new_len;

            self
        }
    }
}

impl Display for String {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        <str as Display>::fmt(self.as_str(), f)
    }
}

struct Vec {
    buf: NonNull<u8>,
    len: usize,
    cap: usize,
    alloc: DefaultAlloc,
}

impl Drop for Vec {
    fn drop(&mut self) {
        // SAFETY: the cap will be valid because we allocated it
        unsafe {
            self.alloc
                .dealloc(self.buf, Layout::from_size_align_unchecked(self.cap, 1));
        }
    }
}
