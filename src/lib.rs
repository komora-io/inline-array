#![allow(unsafe_code)]

use std::{
    alloc::{alloc, dealloc, Layout},
    convert::TryFrom,
    fmt,
    hash::{Hash, Hasher},
    iter::FromIterator,
    mem::size_of,
    ops::Deref,
    sync::atomic::{AtomicUsize, Ordering},
};

const SZ: usize = size_of::<usize>();
const CUTOFF: usize = SZ - 1;

/// A buffer that may either be inline or remote and protected
/// by an Arc. The inner buffer is guaranteed to be aligned to
/// 8 byte boundaries.
#[repr(align(8))]
pub struct InlineArray([u8; SZ]);

impl Clone for InlineArray {
    fn clone(&self) -> InlineArray {
        if !self.is_inline() {
            self.deref_header().rc.fetch_add(1, Ordering::Relaxed);
        }
        InlineArray(self.0)
    }
}

impl Drop for InlineArray {
    fn drop(&mut self) {
        if !self.is_inline() {
            let rc = self.deref_header().rc.fetch_sub(1, Ordering::Release) - 1;

            if rc == 0 {
                let layout =
                    Layout::from_size_align(self.deref_header().len + size_of::<RemoteHeader>(), 8)
                        .unwrap();

                std::sync::atomic::fence(Ordering::Acquire);

                unsafe {
                    dealloc(self.remote_ptr() as *mut u8, layout);
                }
            }
        }
    }
}

struct RemoteHeader {
    rc: AtomicUsize,
    len: usize,
}

impl Deref for InlineArray {
    type Target = [u8];

    #[inline]
    fn deref(&self) -> &[u8] {
        if self.is_inline() {
            &self.0[..self.inline_len()]
        } else {
            unsafe {
                let data_ptr = self.remote_ptr().add(size_of::<RemoteHeader>());
                let len = self.deref_header().len;
                std::slice::from_raw_parts(data_ptr, len)
            }
        }
    }
}

impl AsRef<[u8]> for InlineArray {
    #[inline]
    fn as_ref(&self) -> &[u8] {
        self
    }
}

impl Default for InlineArray {
    fn default() -> Self {
        Self::from(&[])
    }
}

impl Hash for InlineArray {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.deref().hash(state);
    }
}

impl InlineArray {
    fn new(slice: &[u8]) -> Self {
        let mut data = [0_u8; SZ];
        if slice.len() <= CUTOFF {
            data[SZ - 1] = (u8::try_from(slice.len()).unwrap() << 1) | 1;
            data[..slice.len()].copy_from_slice(slice);
        } else {
            let layout =
                Layout::from_size_align(slice.len() + size_of::<RemoteHeader>(), 8).unwrap();

            let header = RemoteHeader {
                rc: 1.into(),
                len: slice.len(),
            };

            unsafe {
                let ptr = alloc(layout);

                std::ptr::write(ptr as *mut RemoteHeader, header);
                std::ptr::copy_nonoverlapping(
                    slice.as_ptr(),
                    ptr.add(size_of::<RemoteHeader>()),
                    slice.len(),
                );
                std::ptr::write_unaligned(data.as_mut_ptr() as _, ptr);
            }

            // assert that the bottom 3 bits are empty, as we expect
            // the buffer to always have an alignment of 8 (2 ^ 3).
            #[cfg(not(miri))]
            assert_eq!(data[SZ - 1] & 0b111, 0);
        }
        Self(data)
    }

    fn remote_ptr(&self) -> *const u8 {
        assert!(!self.is_inline());
        unsafe { std::ptr::read(self.0.as_ptr() as *const *const u8) }
    }

    fn deref_header(&self) -> &RemoteHeader {
        assert!(!self.is_inline());
        unsafe { &*(self.remote_ptr() as *mut RemoteHeader) }
    }

    #[cfg(miri)]
    fn inline_len(&self) -> usize {
        (self.trailer() >> 1) as usize
    }

    #[cfg(miri)]
    fn is_inline(&self) -> bool {
        self.trailer() & 1 == 1
    }

    #[cfg(miri)]
    fn trailer(&self) -> u8 {
        self.deref()[SZ - 1]
    }

    #[cfg(not(miri))]
    const fn inline_len(&self) -> usize {
        (self.trailer() >> 1) as usize
    }

    #[cfg(not(miri))]
    const fn is_inline(&self) -> bool {
        self.trailer() & 1 == 1
    }

    #[cfg(not(miri))]
    const fn trailer(&self) -> u8 {
        self.0[SZ - 1]
    }

    /// This function returns a mutable reference to the inner
    /// byte array. If there are more than 1 atomic references
    /// to the inner array, the array is copied into a new
    /// `InlineVec` and a reference to that is returned. This
    /// functions similarly in spirit to [`std::sync::Arc::make_mut`].
    pub fn make_mut(&mut self) -> &mut [u8] {
        if self.is_inline() {
            let inline_len = self.inline_len();
            &mut self.0[..inline_len]
        } else {
            if self.deref_header().rc.load(Ordering::Acquire) != 1 {
                *self = InlineArray::from(self.deref())
            }
            unsafe {
                let data_ptr = self.remote_ptr().add(size_of::<RemoteHeader>());
                let len = self.deref_header().len;
                std::slice::from_raw_parts_mut(data_ptr as *mut u8, len)
            }
        }
    }
}

impl FromIterator<u8> for InlineArray {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = u8>,
    {
        let bs: Vec<u8> = iter.into_iter().collect();
        bs.into()
    }
}

impl From<&[u8]> for InlineArray {
    fn from(slice: &[u8]) -> Self {
        InlineArray::new(slice)
    }
}

impl From<&str> for InlineArray {
    fn from(s: &str) -> Self {
        Self::from(s.as_bytes())
    }
}

impl From<String> for InlineArray {
    fn from(s: String) -> Self {
        Self::from(s.as_bytes())
    }
}

impl From<&String> for InlineArray {
    fn from(s: &String) -> Self {
        Self::from(s.as_bytes())
    }
}

impl From<&InlineArray> for InlineArray {
    fn from(v: &Self) -> Self {
        v.clone()
    }
}

impl From<Vec<u8>> for InlineArray {
    fn from(v: Vec<u8>) -> Self {
        InlineArray::new(&v)
    }
}

impl From<Box<[u8]>> for InlineArray {
    fn from(v: Box<[u8]>) -> Self {
        InlineArray::new(&v)
    }
}

impl std::borrow::Borrow<[u8]> for InlineArray {
    fn borrow(&self) -> &[u8] {
        self.as_ref()
    }
}

impl std::borrow::Borrow<[u8]> for &InlineArray {
    fn borrow(&self) -> &[u8] {
        self.as_ref()
    }
}

impl<const N: usize> From<&[u8; N]> for InlineArray {
    fn from(v: &[u8; N]) -> Self {
        Self::from(&v[..])
    }
}

impl Ord for InlineArray {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_ref().cmp(other.as_ref())
    }
}

impl PartialOrd for InlineArray {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: AsRef<[u8]>> PartialEq<T> for InlineArray {
    fn eq(&self, other: &T) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl PartialEq<[u8]> for InlineArray {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_ref() == other
    }
}

impl Eq for InlineArray {}

impl fmt::Debug for InlineArray {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}

#[cfg(test)]
mod qc {
    use super::InlineArray;

    #[test]
    fn inline_array_usage() {
        let iv1 = InlineArray::from(vec![1, 2, 3]);
        assert_eq!(iv1, vec![1, 2, 3]);
        let iv2 = InlineArray::from(&[4; 128][..]);
        assert_eq!(iv2, vec![4; 128]);
    }

    #[test]
    fn boxed_slice_conversion() {
        let boite1: Box<[u8]> = Box::new([1, 2, 3]);
        let iv1: InlineArray = boite1.into();
        assert_eq!(iv1, vec![1, 2, 3]);
        let boite2: Box<[u8]> = Box::new([4; 128]);
        let iv2: InlineArray = boite2.into();
        assert_eq!(iv2, vec![4; 128]);
    }

    #[test]
    fn inline_array_as_mut_identity() {
        let initial = &[1];
        let mut iv = InlineArray::from(initial);
        assert_eq!(initial, &*iv);
        assert_eq!(initial, iv.make_mut());
    }

    fn prop_identity(inline_array: &InlineArray) -> bool {
        let mut iv2 = inline_array.clone();

        if iv2 != inline_array {
            println!("expected clone to equal original");
            return false;
        }

        if *inline_array != *iv2 {
            println!("expected AsMut to equal original");
            return false;
        }

        if &*inline_array != iv2.make_mut() {
            println!("expected AsMut to equal original");
            return false;
        }

        true
    }

    impl quickcheck::Arbitrary for InlineArray {
        fn arbitrary(_: &mut quickcheck::Gen) -> Self {
            todo!()
        }
    }

    quickcheck::quickcheck! {
        #[cfg_attr(miri, ignore)]
        fn inline_array(item: InlineArray) -> bool {
            prop_identity(&item)
        }
    }

    #[test]
    fn inline_array_bug_00() {
        assert!(prop_identity(&InlineArray::new(&[
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ])));
    }
}
