use core::fmt;
use ops::DerefMut;
use std::array::IntoIter;
use std::borrow::Cow;
use std::fmt::{Debug, Display, Formatter};
use std::iter::{Map, Take};
use std::mem::MaybeUninit;
use std::ops::{Add, AddAssign, Bound, Deref, Index, IndexMut, RangeBounds, Sub, SubAssign};
use std::ptr::{copy_nonoverlapping, slice_from_raw_parts};
use std::slice::Iter;
use std::slice::{SliceIndex, from_raw_parts, from_raw_parts_mut};
use std::str::{Utf8Error, from_utf8_unchecked};
use std::{ops, ptr};

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum InsertionErr {
    NotEnoughSpace { additional_space_needed: usize },
    OutOfBounds { by: usize },
}

// shamelessly stolen from vec
macro_rules! __impl_slice_eq1 {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty $(where $ty:ty: $bound:ident)?) => {
        impl<T: Copy, U: Copy, $($vars)*> PartialEq<$rhs> for $lhs
        where
            T: PartialEq<U>,
            $($ty: $bound)?
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { self[..] == other[..] }
            #[inline]
            fn ne(&self, other: &$rhs) -> bool { self[..] != other[..] }
        }
    }
}

macro_rules! __impl_cvec_eq {
    ($name0: ident, $name1: ident) => {
        __impl_slice_eq1! { [const N: usize, const M: usize] $name0<T, N>, $name1<U, M> }
    };
}
macro_rules! __define_cvec {
    ($name: ident, $len_type:ty) => {
        #[doc = concat!("A heapless Vec with a fixed capacity in the range [0..=[",stringify!($len_type),"::MAX]] that can only hold [Copy] elements (and is therefore `Copy` itself). Its name is short for \"Copyable Vector indexed by ", stringify!($len_type), "\".")]
        pub struct $name<T: Copy, const N: usize> {
            len: $len_type,
            buf: [MaybeUninit<T>; N],
        }
        impl<T: Copy, const N: usize> $name<T, N> {
            /// Returns the amount of elements currently stored, as a usize.
            #[inline]
            #[must_use]
            pub const fn len(&self) -> usize {
                self.len as usize
            }

            /// Returns true if `len >= N`.
            #[inline]
            pub const fn is_full(&self) -> bool {
                self.len() >= N
            }

            /// Sets `len` to 0, does not write to the buffer itself
            #[inline]
            pub const fn clear(&mut self) {
                self.len = 0;
            }

            /// Clears the vector and sets every element in the array (initialized or not) to zero, using [ptr::write_volatile].
            #[inline(always)]
            pub fn zeroize(&mut self) {
                self.clear();
                let buf_start = self.buf.as_mut_ptr();
                let zero: MaybeUninit<T> = MaybeUninit::zeroed();
                let mut i = 0;
                while i < N {
                    // SAFETY: `i` is inside [0..N] so `ptr` points to memory inside `buf`
                    let ptr = unsafe { buf_start.add(i) };

                    // SAFETY: we're setting a MaybeUninit<T> array element to a MaybeUninit<T> value
                    unsafe { ptr::write_volatile(ptr, zero) };
                    i += 1;
                }
            }

            /// Fill empty spaces with `val`. The vector ends up holding `N` elements. Does nothing if already full.
            #[inline]
            pub const fn fill_remaining(&mut self, val: T) {
                if self.is_full() {
                    return;
                }
                let len = self.len();
                // SAFETY: we're splitting `self.buf` at `self.len`, and `self.len <= N` is always true
                let (_, empty) = unsafe { self.buf.split_at_mut_unchecked(len) };
                let p: *mut T = empty.as_mut_ptr().cast();
                let mut i = 0;
                let spaces_to_fill = empty.len();
                while i < spaces_to_fill {
                    // SAFETY: [ len ][ empty_spaces ]
                    //                [   p.add(i)   ] -> always within buf
                    //         [        buf          ]
                    unsafe {
                        p.add(i).write(val);
                    }
                    i += 1;
                }
                self.len = N as $len_type;
            }
            /// returns `Some` if `len == N`
            #[inline]
            pub const fn try_as_array(&self) -> Option<&[T; N]> {
                if self.is_full() {
                    // SAFETY: self.buf is completely initialized
                    Some(unsafe { self.as_array_unchecked() })
                } else {
                    None
                }
            }
            /// returns `Some` if `len == N`
            #[inline]
            pub const fn try_as_array_mut(&mut self) -> Option<&mut [T; N]> {
                if self.is_full() {
                    // SAFETY: buf is completely initialized
                    Some(unsafe { self.as_array_mut_unchecked() })
                } else {
                    None
                }
            }

            /// SAFETY: safe when self.len >= N
            #[inline]
            pub const unsafe fn as_array_unchecked(&self) -> &[T; N] {
                unsafe { &*(self.as_ptr() as *const [T; N]) }
            }
            /// SAFETY: safe when self.len >= N
            #[inline]
            pub const unsafe fn as_array_mut_unchecked(&mut self) -> &mut [T; N] {
                unsafe { &mut *(self.as_mut_ptr() as *mut [T; N]) }
            }

            /// Returns Some only when the vec contains at least N elements
            #[inline]
            pub const fn into_array_if_full(self) -> Option<[T; N]> {
                if N <= self.len() {
                    Some(unsafe { self.into_array_unchecked() })
                } else {
                    None
                }
            }

            /// If the vec contains fewer than N elements, it will fill the remaining with `fill_empty_with`
            #[inline]
            pub const fn to_array_fill_empty(&self, fill_empty_with: T) -> [T; N] {
                if self.is_full() {
                    // SAFETY: is_full -> array is initialized
                    return unsafe { self.into_array_unchecked() };
                }
                let mut buf = self.buf;

                let p: *mut T = buf.as_mut_ptr().cast();
                let mut i = self.len();
                while i < N {
                    //  SAFETY: `i` is in the bounded range of [self.len, N)
                    unsafe { p.add(i).write(fill_empty_with) }
                    i += 1;
                }

                // SAFETY: ret is fully initialized
                unsafe { assume_init_read(&buf) }
            }

            /// SAFETY: safe when self.len >= N
            #[inline]
            pub const unsafe fn into_array_unchecked(self) -> [T; N] {
                unsafe { assume_init_read(&self.buf) }
            }

            /// Panics if not full
            #[inline]
            pub const fn into_array_or_panic(self) -> [T; N] {
                assert!(self.len() >= N);
                unsafe { self.into_array_unchecked() }
            }
            /// Returns an empty vec
            #[inline]
            pub const fn new() -> Self {
                const { assert!(
                    N <= <$len_type> :: MAX_USIZE,
                    concat!("N should not be greater than ", stringify!($len_type),"::MAX, either choose a lower N or a higher len_type.")
                ) }
                Self {
                    buf: [const { MaybeUninit::uninit() }; N],
                    len: 0,
                }
            }

            /// Performs bounds check
            #[inline]
            pub const fn get(&self, index: usize) -> Option<&T> {
                if index >= self.len() {
                    return None
                }
                return Some(unsafe{self.get_unchecked(index)})
            }

            /// Performs bounds check
            #[inline]
            pub const fn get_mut(&mut self, index: usize) -> Option<&mut T> {
                if index >= self.len() {
                    return None
                }
                return Some(unsafe{self.get_unchecked_mut(index)})
            }

            /// Performs bounds check
            #[inline]
            pub const fn get_read(&self, index: usize) -> Option<T> {
                if index >= self.len() {
                    return None
                }
                return Some(unsafe{self.get_unchecked_read(index)})
            }

            /// Performs no bounds check
            #[inline]
            pub const unsafe fn get_unchecked(&self, index: usize) -> &T {
                unsafe { self.buf[index].assume_init_ref() }
            }
            /// Performs no bounds check
            #[inline]
            pub const unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
                unsafe { self.buf[index].assume_init_mut() }
            }
            /// Performs no bounds check and returns a copy
            #[inline]
            pub const unsafe fn get_unchecked_read(&self, index: usize) -> T {
                unsafe { self.buf[index].assume_init_read() }
            }
            /// Panics if full
            #[inline]
            pub const fn push_or_panic(&mut self, element: T) {
                let _ = self.push_mut_or_panic(element);
            }
            /// Returns the pushed element, panics if full
            #[inline]
            #[must_use = "if you don't need a reference to the value, use `push_or_panic` instead"]
            pub const fn push_mut_or_panic(&mut self, element: T) -> &mut T {
                let e = &mut self.buf[self.len()];
                *e = MaybeUninit::new(element);
                self.len += 1;
                // SAFETY: we just assigned it to something
                unsafe { e.assume_init_mut() }
            }
            /// Returns an Err with the element if already full
            #[inline]
            pub const fn push_within_capacity(&mut self, element: T) -> Result<(), T> {
                if self.is_full() {
                    return Err(element)
                }
                // SAFETY: we just confirmed we got room
                unsafe { self.push_unchecked(element) };
                Ok(())

            }


            /// Safe when it's not full
            #[inline]
            pub const unsafe fn push_unchecked(&mut self, element: T) {
                unsafe {
                    self.buf
                        .as_mut_ptr()
                        .add(self.len())
                        .write(MaybeUninit::new(element))
                };
                self.len += 1;
            }

            /// Returns an Err with the element if already full
            #[inline]
            pub const fn push_front_within_capacity(&mut self, element: T) -> Result<(), T> {
                self.insert_within_capacity(0, element)
            }

            /// Returns an Err with the element if already full or out of bounds
            #[inline]
            pub const fn insert_within_capacity(&mut self, at: usize, element: T) -> Result<(), T> {
                if !self.is_insert_ok(at) {
                    return Err(element)
                }

                unsafe {
                    let ptr = self.as_mut_ptr();
                    let count = self.len()-at;
                    let dest = at + 1;
                    let src_ptr = ptr.add(at);
                    let dest_ptr = ptr.add(dest);
                    if count > 0 {
                        ptr::copy(src_ptr, dest_ptr, count);
                    }
                    ptr::write(src_ptr, element);
                    self.len += 1;
                }

                Ok(())
            }

            /// Returns an InsertionError if full or out of bounds
            #[inline]
            pub const fn insert_slice_within_capacity(&mut self, at: usize, elements: &[T]) -> Result<(), InsertionErr> {
                let len = self.len();
                if len < at { // out of bounds
                    return Err(InsertionErr::OutOfBounds {by:at-len})
                }
                let insert_count = elements.len();
                if insert_count == 0 { // empty slice ok
                    return Ok(())
                }
                let new_len = len + insert_count;
                if new_len > N { // full
                    return Err(InsertionErr::NotEnoughSpace {additional_space_needed: new_len - N})
                }

                unsafe {
                    let ptr = self.as_mut_ptr();
                    let elements_to_shift_to_the_right = len - at;
                    let insertion_point = ptr.add(at);
                    let shifted_elements_new_start_point = ptr.add(at + insert_count);
                    if elements_to_shift_to_the_right > 0 {
                        ptr::copy(insertion_point, shifted_elements_new_start_point, elements_to_shift_to_the_right);
                    }
                    ptr::copy_nonoverlapping(elements.as_ptr(), insertion_point, insert_count);
                    self.len += insert_count as $len_type;
                }

                Ok(())
            }

            /// Returns an InsertionError if full or out of bounds
            #[inline]
            pub const fn push_slice_within_capacity(&mut self, elements: &[T]) -> Result<(), InsertionErr> {
                self.insert_slice_within_capacity(self.len(), elements)
            }

            /// Casts a reference to the buf array as a pointer to T
            #[inline]
            pub const fn as_ptr(&self) -> *const T {
                self.buf.as_ptr().cast::<T>()
            }
            /// Casts a reference to the buf array as a mut pointer to T
            #[inline]
            pub const fn as_mut_ptr(&mut self) -> *mut T {
                self.buf.as_mut_ptr().cast::<T>()
            }
            /// Returns a slice with the elements of the occupied range.
            #[inline]
            pub const fn as_slice(&self) -> &[T] {
                unsafe { from_raw_parts(self.as_ptr(), self.len()) }
            }
            /// Returns a mutable slice with the elements of the occupied range.
            #[inline]
            pub const fn as_mut_slice(&mut self) -> &mut [T] {
                unsafe { from_raw_parts_mut(self.as_mut_ptr(), self.len()) }
            }

            /// Error contains a subslice of the elements that do fit (it doesn't append them)
            #[inline]
            pub const fn try_append_slice<'a>(&mut self, other: &'a [T]) -> Result<(), &'a [T]> {
                let len = self.len();
                let space_available = N - len;
                let space_needed = other.len();
                if space_needed > space_available {
                    let ptr = slice_from_raw_parts(other.as_ptr(), space_available);
                    // SAFETY: `other[..space_available].len() <= other[..].len()`
                    let slice_that_fits = unsafe { &*ptr };
                    return Err(slice_that_fits);
                };

                // SAFETY: `other[..].len() <= self.buf[len..].len()`
                unsafe { copy_nonoverlapping(other.as_ptr(), self.as_mut_ptr().add(len), space_needed) };
                self.len += space_needed as $len_type;
                Ok(())
            }

            /// Return value contains the subslice that did not fit
            #[inline]
            pub const fn append_slice_or_crop<'a>(&mut self, other: &'a [T]) -> Option<&'a [T]> {
                let len = self.len();
                let space_available = N - len;
                let space_needed = other.len();
                if space_needed > space_available {
                    let (keepit, returnit) = unsafe { other.split_at_unchecked(space_available) };

                    // SAFETY: `other[..space_available].len() <= other[..].len()`
                    let slice_that_fits =
                        unsafe { &*slice_from_raw_parts(keepit.as_ptr(), space_available) };
                    unsafe { self.append_slice_unchecked(slice_that_fits) };
                    return Some(returnit);
                };

                // SAFETY: `other.len() <= space_available`
                unsafe { copy_nonoverlapping(other.as_ptr(), self.as_mut_ptr().add(len), space_needed) };
                self.len += space_needed as $len_type;
                None
            }

            /// Panics if it cannot contain the slice.
            #[inline]
            pub const fn append_slice_or_panic(&mut self, other: &[T]) {
                let count = other.len();
                let len = self.len();

                let size_needed = count + len;
                assert!(size_needed <= N, "capacity reached!");

                unsafe { copy_nonoverlapping(other.as_ptr(), self.as_mut_ptr().add(len), count) };
                self.len += count as $len_type;
            }

            /// Performs no bounds check. Safe only when `self.len()+slice.len() <= N`.
            #[inline]
            pub const unsafe fn append_slice_unchecked(&mut self, slice: &[T]) {
                let count = slice.len();
                let len = self.len();

                unsafe { copy_nonoverlapping(slice.as_ptr(), self.as_mut_ptr().add(len), count) };
                self.len += count as $len_type;
            }
            /// Panics when `slice.len() > N`
            #[inline]
            pub const fn from_slice_or_panic(slice: &[T]) -> Self {
                let mut ret = Self::new();
                ret.append_slice_or_panic(slice);
                ret
            }
            /// Performs no bounds check. Safe only when `slice.len() <= N`.
            #[inline]
            pub const unsafe fn from_slice_unchecked(other: &[T]) -> Self {
                let mut ret = Self::new();
                unsafe { ret.append_slice_unchecked(other) };
                ret
            }
            /// Ignores elements outside of `slice[0..N]`
            #[inline]
            pub const fn from_slice_or_crop(slice: &[T]) -> Self {
                let slice = if let Some((cropped, _)) = slice.split_at_checked(N) {
                    cropped
                } else {
                    slice
                };
                // SAFETY: slice is cropped to len <= N
                unsafe { Self::from_slice_unchecked(slice) }
            }
            /// Removes elements where `f(e)` is false
            #[inline]
            pub fn retain<F>(&mut self, mut predicate: F)
            where
                F: FnMut(&T) -> bool,
            {
                self.retain_mut(|it| predicate(it))
            }

            /// Removes elements where `f(e)` is false, predicate can modify items.
            #[inline]
            pub fn retain_mut<F>(&mut self, predicate: F)
            where
                F: FnMut(&mut T) -> bool,
            {
                let kept = slice_retain_in_place(self.as_mut_slice(), predicate);
                self.len = kept.len() as $len_type;
            }

            /// Returns the amount of elements that can be added to the vec before it's full.
            #[inline]
            pub const fn remaining_capacity(&self) -> usize {
                N - self.len()
            }

            /// Creates a full vec of capacity N from an array of length N
            #[inline]
            pub const fn from_array_as_full(other: &[T; N]) -> Self {
                Self {
                    buf: unsafe { *other.as_ptr().cast::<[MaybeUninit<T>; N]>() },
                    len: N as $len_type,
                }
            }

            /// Removes the last element and returns it
            #[inline]
            pub const fn pop(&mut self) -> Option<T> {
                if self.len > 0 {
                    self.len -= 1;
                    let ret = self.buf[self.len()];
                    Some(unsafe { ret.assume_init() })
                } else {
                    None
                }
            }

            /// Removes the first element and returns it
            #[inline]
            pub const fn pop_front(&mut self) -> Option<T>{
                if self.len == 0 {
                    return None
                }
                let ret = unsafe{self.get_unchecked_read(0)};
                self.remove(0);
                Some(ret)
            }

            /// Removes the nth element and returns it
            #[inline]
            pub const fn pop_at(&mut self, index: usize) -> Option<T>{
                if !self.is_read_ok(index) {
                    return None
                }
                let ret = unsafe{ self.get_unchecked_read(index) };
                self.remove(index);
                Some(ret)
            }


            #[inline]
            const fn is_read_ok(&self, index: usize) -> bool{
                self.len() > index
            }


            #[inline]
            const fn is_insert_ok(&self, index: usize) -> bool{
                self.len() >= index && !self.is_full()
            }

            #[inline]
            pub fn remove_range<R: RangeBounds<usize>>(&mut self, range: R) {
                use Bound::*;
                let len = self.len();
                let start = match range.start_bound() {
                    Included(n) => *n,
                    Excluded(n) => n.checked_add(1).expect("out of bounds!"),
                    Unbounded => 0,
                };
                let end_exclusive = match range.end_bound() {
                    Included(n) => n.checked_add(1).expect("out of bounds!"),
                    Excluded(n) => *n,
                    Unbounded => len,
                };
                assert!(start <= end_exclusive, "out of bounds!");
                self.remove_contiguous_or_panic(start, end_exclusive - start);
            }

            /// Before:
            /// ```text
            /// visible slice:
            /// "I can't ...NOT!!!!believe it's NOT HEAP!"
            /// backing array:
            /// "I can't ...NOT!!!!believe it's NOT HEAP!_____________"
            ///  [ used                                 ][ available ]
            ///          |start    |end                  |len         |N
            ///  [ keep ][ remove ][ elements to shift  ][ uninit    ]
            /// ```
            /// After:
            /// ```text
            /// visible slice:
            /// "I can't believe it's NOT HEAP!"
            /// backing array:
            /// "I can't believe it's NOT HEAP! NOT HEAP!_____________"
            ///  [ used                       ][ available           ]
            ///                                |len                   |N
            ///  [ keep ][ shifted elements   ][ freed  ][ uninit    ]
            /// ```

            #[inline]
            pub const fn remove_contiguous_or_panic(&mut self, start: usize, count: usize) {
                let len = self.len();

                let end = start + count;
                assert!(end <= len, "out of bounds!");
                if count == 0 {
                    return;
                }
                self.len -= count as $len_type;
                if end == len {
                    // we're deleting elements at the end so no shift needed
                    return;
                }

                let start = start as usize;
                let end = end as usize;
                let elements_to_shift = (len as usize) - end;

                let ptr_to_0 = self.as_mut_ptr();

                // SAFETY: end < self.len
                let src: *const T = unsafe { ptr_to_0.add(end) };
                // SAFETY: index < self.len
                let dst: *mut T = unsafe { ptr_to_0.add(start) };
                // SAFETY: src.add(elements_to_shift) points to the end of the buf
                unsafe { ptr::copy(src, dst, elements_to_shift) };
            }

            #[inline]
            pub const fn remove(&mut self, element: usize) {
                self.remove_contiguous_or_panic(element, 1);
            }

            #[inline]
            pub const fn from_elem(elem: T) -> Self {
                let elem: MaybeUninit<T> = MaybeUninit::new(elem);
                Self {
                    len: N as $len_type,
                    buf: [elem; N],
                }
            }

            #[inline]
            pub const fn from_elem_up_to_or_panic(elem: T, n: usize) -> Self {
                assert!(n <= N, "n should be greater than N");
                Self {
                    len: n as $len_type,
                    buf: {
                        let mut buf = [MaybeUninit::uninit(); N];
                        unsafe { fill_unchecked(buf.as_mut_ptr(), MaybeUninit::new(elem), n as usize) };
                        buf
                    },
                }
            }

            #[inline]
            pub fn map<F, U>(&self, f: F) -> $name<U, N>
            where
                F: FnMut(T) -> U,
                U: Copy,
            {
                $name::<U, N>::from_iter(self.into_iter().copied().map(f))
            }

        }
        /// Common methods for str handling
        impl<const N: usize> $name<u8, N> {
            #[inline]
            pub const fn from_str_or_panic(p0: &str) -> Self {
                Self::from_slice_or_panic(p0.as_bytes())
            }
            #[inline]
            pub const fn from_str_or_crop(p0: &str) -> Self {
                // SAFETY: `p0.floor_char_boundary` will always return an index within `[0, p0.len]`
                let (fits, _) = p0.split_at(p0.floor_char_boundary(N));
                Self::from_str_or_panic(fits)
            }
            #[inline]
            pub const fn as_str_or_panic(&self) -> &str {
                if let Ok(r) = self.as_str() {
                    r
                } else {
                    panic!("this cvec cannot be converted to &str")
                }
            }
            #[inline]
            pub const fn as_str(&self) -> Result<&str, Utf8Error> {
                str::from_utf8(self.as_slice())
            }
            #[inline]
            pub const fn as_str_mut(&mut self) -> Result<&mut str, Utf8Error> {
                str::from_utf8_mut(self.as_mut_slice())
            }
            #[inline]
            pub const unsafe fn as_str_unchecked(&self) -> &str {
                unsafe { str::from_utf8_unchecked(self.as_slice()) }
            }
            #[inline]
            pub const unsafe fn as_str_mut_unchecked(&mut self) -> &mut str {
                unsafe { str::from_utf8_unchecked_mut(self.as_mut_slice()) }
            }

            #[inline]
            pub const fn push_str_or_panic(&mut self, s: &str) {
                self.append_slice_or_panic(s.as_bytes());
            }
            #[inline]
            pub const unsafe fn push_str_unchecked(&mut self, s: &str) {
                // SAFETY: s should fit
                unsafe { self.append_slice_unchecked(s.as_bytes()) };
            }
            /// On error, it returns `(part_that_fits, part_that_does_not_fit)`, and `part_that_fits` is NOT appended.
            #[inline]
            pub const fn try_push_str<'a>(&mut self, s: &'a str) -> Result<(), (&'a str, &'a str)> {
                let bytes = s.as_bytes();
                if let Err(r) = self.try_append_slice(bytes) {
                    let boundary = s.floor_char_boundary(r.len());
                    let (fits, not_fits) = unsafe { bytes.split_at_unchecked(boundary) };
                    Err(unsafe { (from_utf8_unchecked(fits), from_utf8_unchecked(not_fits)) })
                } else {
                    Ok(())
                }
            }
            /// Return value contains the substring that did not fit
            #[inline]
            pub const fn push_str_or_crop<'a>(&mut self, s: &'a str) -> Option<&'a str> {
                if let Err((fits, fits_not)) = self.try_push_str(s) {
                    // SAFETY: fits is guaranteed to fit
                    unsafe { self.push_str_unchecked(fits) };
                    Some(fits_not)
                } else {
                    None
                }
            }

            /// If the char fits, returns `Ok(bytes_written)`.
            /// If the char doesn't fit, returns `Err(excess_bytes)`
            #[inline]
            pub const fn push_char_if_possible(&mut self, c: char) -> Result<usize, usize> {
                let rem = self.remaining_capacity();
                let clen = c.len_utf8();
                if clen <= rem {
                    let mut scratch_buffer = [0u8; 4];
                    let utf8_bytes = c.encode_utf8(&mut scratch_buffer).as_bytes();
                    unsafe { self.append_slice_unchecked(&utf8_bytes) };
                    Ok(clen)
                } else {
                    Err(clen - rem)
                }
            }
        }
        impl<T: Clone + Copy, const N: usize> Clone for $name<T, N> {
            fn clone(&self) -> Self {
                Self {
                    len: self.len,
                    buf: {
                        let mut ret = [MaybeUninit::uninit(); _];
                        unsafe {
                            copy_nonoverlapping(self.as_ptr(), ret.as_mut_ptr().cast(), self.len())
                        };
                        ret
                    },
                }
            }
        }

        impl<T: Copy, const N: usize> IntoIterator for $name<T, N> {
            type Item = T;
            type IntoIter = Map<Take<IntoIter<MaybeUninit<T>, N>>, fn(MaybeUninit<T>) -> T>;

            fn into_iter(self) -> Self::IntoIter {
                self.buf
                    .into_iter()
                    .take(self.len())
                    .map(|maybe_uninit| unsafe { maybe_uninit.assume_init() })
            }
        }

        impl<'a, T: Copy, const N: usize> IntoIterator for &'a $name<T, N> {
            type Item = &'a T;
            type IntoIter = Map<Take<Iter<'a, MaybeUninit<T>>>, fn(&MaybeUninit<T>) -> &T>;

            fn into_iter(self) -> Self::IntoIter {
                self.buf
                    .iter()
                    .take(self.len())
                    .map(|maybe_uninit| unsafe { maybe_uninit.assume_init_ref() })
            }
        }



        impl<T: Copy, const N: usize> FromIterator<T> for $name<T, N> {
            /// Will panic if the iter contains more elements than the capacity
            fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
                let mut ret = Self::new();
                let mut i = 0;
                for t in iter {
                    assert!(i < N, "iterator contains more than {} elements", N);
                    ret.buf[i] = MaybeUninit::new(t);
                    i += 1;
                }
                ret.len = i as $len_type;
                ret
            }
        }
        impl<T: Copy, const N: usize> Copy for $name<T, N> {}
        impl<T: Copy + Eq, const N: usize> Eq for $name<T, N> {}

        impl<T: Copy, const N: usize> Default for $name<T, N> {
            #[inline]
            fn default() -> Self {
                Self {
                    buf: [MaybeUninit::uninit(); N],
                    len: 0,
                }
            }
        }
        impl<T: Copy, const N: usize> Deref for $name<T, N> {
            type Target = [T];

            #[inline]
            fn deref(&self) -> &[T] {
                self.as_slice()
            }
        }

        impl<T: Copy, const N: usize> DerefMut for $name<T, N> {
            #[inline]
            fn deref_mut(&mut self) -> &mut [T] {
                self.as_mut_slice()
            }
        }
        impl<T: Copy + Debug, const N: usize> Debug for $name<T, N> {
            fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
                Debug::fmt(&**self, f)
            }
        }
        impl<T: Copy, I: SliceIndex<[T]>, const N: usize> Index<I> for $name<T, N> {
            type Output = I::Output;

            #[inline]
            fn index(&self, index: I) -> &Self::Output {
                Index::index(self.as_slice(), index)
            }
        }
        impl<T: Copy, I: SliceIndex<[T]>, const N: usize> IndexMut<I> for $name<T, N> {
            #[inline]
            fn index_mut(&mut self, index: I) -> &mut Self::Output {
                IndexMut::index_mut(self.as_mut_slice(), index)
            }
        }
        impl<T: Copy, const N: usize> Extend<T> for $name<T, N> {
            #[inline]
            fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
                for elem in iter {
                    self.push_or_panic(elem);
                }
            }
        }
        impl<'a, T: Copy, const N: usize> Extend<&'a T> for $name<T, N> {
            fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
                for elem in iter {
                    self.push_or_panic(*elem);
                }
            }
        }


        __impl_cvec_eq! { $name, CVec8 }
        __impl_cvec_eq!{ $name, CVec16 }
        __impl_cvec_eq!{ $name, CVec32 }
        __impl_cvec_eq!{ $name, CVec64 }
        __impl_cvec_eq!{ $name, CVec }
        __impl_slice_eq1! { [const N: usize] $name<T, N>, &[U] }
        __impl_slice_eq1! { [const N: usize] $name<T, N>, &mut [U] }
        __impl_slice_eq1! { [const M: usize] &[T], $name<U, M> }
        __impl_slice_eq1! { [const M: usize] &mut [T], $name<U, M> }
        __impl_slice_eq1! { [const N: usize] $name<T, N>, [U]  }
        __impl_slice_eq1! { [const M: usize] [T], $name<U, M>  }
        __impl_slice_eq1! { [const M: usize] Cow<'_, [T]>, $name<U, M> }
        __impl_slice_eq1! { [const N: usize, const M: usize] $name<T, N>, [U; M] }
        __impl_slice_eq1! { [const N: usize, const M: usize] $name<T, N>, &[U; M] }
        __impl_slice_eq1! { [const N: usize, const M: usize] $name<T, N>, &mut [U; M]}
        __impl_slice_eq1! { [const N: usize, const M: usize] [T; N], $name<U, M>}
        __impl_slice_eq1! { [const N: usize, const M: usize] &[T; N], $name<U, M>}
        __impl_slice_eq1! { [const N: usize, const M: usize] &mut [T; N], $name<U, M>}
        impl<const N: usize> PartialEq<str> for $name<u8, N> {
            #[inline]
            fn eq(&self, other: &str) -> bool {
                self[..] == other.as_bytes()[..]
            }
            #[inline]
            fn ne(&self, other: &str) -> bool {
                self[..] != other.as_bytes()[..]
            }
        }
        impl<const N: usize> PartialEq<&str> for $name<u8, N> {
            #[inline]
            fn eq(&self, other: &&str) -> bool {
                self[..] == other.as_bytes()[..]
            }
            #[inline]
            fn ne(&self, other: &&str) -> bool {
                self[..] != other.as_bytes()[..]
            }
        }
        impl<const N: usize> fmt::Write for $name<u8, N> {
            // crops if it doesn't fit, never panics
            #[inline]
            fn write_str(&mut self, s: &str) -> fmt::Result {
                self.push_str_or_crop(s);
                Ok(())
            }

            // does nothing if it doesn't fit, never panics
            #[inline]
            fn write_char(&mut self, c: char) -> fmt::Result {
                // result ignored on purpose because it's ok if the char doesn't fit the buffer
                let _ = self.push_char_if_possible(c);
                Ok(())
            }
        }
    };
}

macro_rules! __define_cvec_macros {
    (($d:tt) $t:ident, $name:ident, $namepriv: ident, $namestr:ident, $namestrpriv: ident) => {
        pub mod $name {
            #[doc = concat!("Creates a [`", stringify!($t) , "`] containing the arguments.")]
            ///
            /// The format is `[element_list; initial_length; N]`
            /// - `*` means `element_list.len()`
            /// - `_` means `N inferred from context`
            ///
            /// So:
            #[doc = concat!(" - `",stringify!($name),"![; *; _]` creates an empty `",stringify!($t),"<_, _>`")]
            #[doc = concat!(" - `",stringify!($name),"![]` is a shortcut for `",stringify!($name),"![; *; _]`")]
            #[doc = concat!(" - `",stringify!($name),"!['a', 'b'; *; _]` creates a `",stringify!($t),"<char, _>` with `len=2`")]
            #[doc = concat!(" - `",stringify!($name),"!['a', 'b']` is a shortcut for `",stringify!($name),"!['a', 'b'; *; _]`")]
            #[doc = concat!(" - `",stringify!($name),"!['a', 'b'; *; 5]` creates a `",stringify!($t),"<char, 5>` that contains 'a' and 'b' (so `len=2`")]
            #[doc = concat!(" - `",stringify!($name),"!['a'; _; 5]` creates a `",stringify!($t),"<char, 5>` that contains 'a' repeated 5 times")]
            #[doc = concat!(" - `",stringify!($name),"!['a'; 3; 5]` creates a `",stringify!($t),"<char, 5>` that contains 'a' repeated 3 times")]
            #[doc = concat!(" - `",stringify!($name),"!['a', 'b'; *; *]` creates a `",stringify!($t),"<char, 2>` with `len=2` and the elements 'a' and 'b'")]

            #[macro_export]
            macro_rules! $namepriv {
                () => (
                    $crate::$t::new()
                );
                (; *; _) => (
                    $crate::$t::new()
                );
                (; *; $n:expr) => (
                    $crate::$t::<_, $n>::new()
                );
                ($d($x:expr),+ $d(,)?; *; _) => (
                    $crate::$t::<_, _>::from_slice_or_panic(&[$d($x,)*])
                );
                ($d($x:expr),+ $d(,)?; *; *) => (
                    $crate::$t::<_, _>::from_array_as_full(&[$d($x,)*])
                );
                ($d($x:expr),+ $d(,)?; *; $n:expr) => (
                    $crate::$t::<_, $n>::from_slice_or_panic(&[$d($x,)*])
                );
                ($elem:expr; _; _) => (
                    $crate::$t::from_elem($elem)
                );
                ($elem:expr; _; $n:expr) => (
                    $crate::$t::<_, $n>::from_elem($elem)
                );
                ($d($x:expr),+ $d(,)?) => (
                    $crate::$t::<_, _>::from_slice_or_panic(&[$d($x,)*])
                );
                ($elem:expr; $n:expr; _) => (
                    $crate::$t::from_elem_up_to_or_panic($elem, $n)
                );
                ($elem:expr; $n:expr; $N:expr) => (
                    $crate::$t::<_, $N>::from_elem_up_to_or_panic($elem, $n)
                );
            }
            pub use $namepriv as $name;

            #[macro_export]
            macro_rules! $namestrpriv {
                () => {
                    $crate::$t::<u8, _>::new()
                };
                (; $n:expr) => {
                    $crate::$t::<u8, $n>::new()
                };
                ($x:expr) => {
                    $crate::$t::<u8, _>::from_str_or_panic($x)
                };
                ($x:expr; $n: expr) => {
                    $crate::$t::<u8, $n>::from_str_or_panic($x)
                };
            }

            pub use $namestrpriv as $namestr;
        }
    };

    ($($name: ident),*) => {
        __define_cvec_macros!{($) $($name),*}
    };
}

__define_cvec!(CVec8, u8);
__define_cvec_macros! {CVec8, cvec8, __cvec8, cvec8str, __cvec8str}

__define_cvec!(CVec16, u16);
__define_cvec_macros! {CVec16, cvec16, __cvec16, cvec16str, __cvec16str}

__define_cvec!(CVec32, u32);
__define_cvec_macros! {CVec32, cvec32, __cvec32, cvec32str, __cvec32str}

__define_cvec!(CVec64, u64);
__define_cvec_macros! {CVec64, cvec64, __cvec64, cvec64str, __cvec64str}

__define_cvec!(CVec, usize);
__define_cvec_macros! {CVec, cvec, __cvec, cvecstr, __cvectsr}

#[inline]
const unsafe fn fill_unchecked<T: Copy>(dst: *mut T, elem: T, count: usize) {
    let mut i = 0;
    while i < count {
        unsafe {
            dst.add(i).write(elem);
        }
        i += 1;
    }
}

/// Filters elements in-place, the returned slice contains the elements for which the predicate is true.
/// The rest of the input slice (not contained within the return value) does not necessarily contain the elements for which the predicate is false.
/// If such an outcome is desired, use one of the "partition_by..." functions.
fn slice_retain_in_place<T: Copy, F>(s: &mut [T], mut pred: F) -> &mut [T]
where
    F: FnMut(&mut T) -> bool,
{
    let total_count = s.len();
    let mut false_count = 0;
    for i in 0..total_count {
        let e = unsafe { s.get_unchecked_mut(i) };
        if pred(e) {
            if false_count > 0 {
                *unsafe { s.get_unchecked_mut(i - false_count) } = *e;
            }
        } else {
            false_count += 1;
        }
    }

    unsafe { s.split_at_mut_unchecked(total_count - false_count).0 }
}

#[inline]
const unsafe fn assume_init_read<T: Copy, const N: usize>(
    maybe_uninit: &[MaybeUninit<T>; N],
) -> [T; N] {
    unsafe { *maybe_uninit.as_ptr().cast::<[T; N]>() }
}

trait Sealed:
    Send
    + Sync
    + Copy
    + Display
    + Debug
    + PartialEq
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + PartialOrd
    + TryFrom<usize, Error: Debug>
    + TryInto<usize, Error: Debug>
{
    /// The zero value of the integer type.
    const ZERO: Self;
    /// The one value of the integer type.
    const MAX: Self;
    /// The maximum value of this type, as a `usize`.
    const MAX_USIZE: usize;

    /// The one value of the integer type.
    ///
    /// It's a function instead of constant because we want to have implementation which panics for
    /// type `ZeroLenType`
    fn one() -> Self;

    /// An infallible conversion from `usize` to `LenT`.
    #[inline]
    fn from_usize(val: usize) -> Self {
        val.try_into().unwrap()
    }

    /// An infallible conversion from `LenT` to `usize`.
    #[inline]
    fn into_usize(self) -> usize {
        self.try_into().unwrap()
    }

    /// Converts `LenT` into `Some(usize)`, unless it's `Self::MAX`, where it returns `None`.
    #[inline]
    fn to_non_max(self) -> Option<usize> {
        if self == Self::MAX {
            None
        } else {
            Some(self.into_usize())
        }
    }
}

macro_rules! impl_lentype {
    ($($(#[$meta:meta])* $LenT:ty),*) => {$(
        $(#[$meta])*
        impl Sealed for $LenT {
            const ZERO: Self = 0;
            const MAX: Self = Self::MAX;
            const MAX_USIZE: usize = Self::MAX as _;

            fn one() -> Self {
                1
            }
        }
    )*}
}

impl_lentype!(u8, u16, u32, u64, usize);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cvec::cvec;
    use core::fmt::Write as _;
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::ptr::slice_from_raw_parts;

    fn assert_panics(f: impl FnOnce()) {
        assert!(catch_unwind(AssertUnwindSafe(f)).is_err());
    }

    #[test]
    fn test_len() {
        let empty: CVec<u8, 0> = cvec!();
        let partial: CVec<u8, 3> = cvec![1, 2; *; 3];
        let full: CVec<u8, 2> = cvec![7, 8; *; 2];
        assert_eq!(empty.len(), 0);
        assert_eq!(partial.len(), 2);
        assert_eq!(full.len(), 2);
    }

    #[test]
    fn test_is_full() {
        let empty: CVec<u8, 0> = cvec!();
        assert!(empty.is_full());
        assert!(!cvec![1, 2; *; 3].is_full());
        assert!(cvec![1, 2; *; 2].is_full());
    }

    #[test]
    fn test_clear() {
        let mut v: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        v.clear();
        v.clear();
        assert_eq!(v.len(), 0);
        assert_eq!(v.as_slice(), &[]);
    }

    #[test]
    fn test_zeroize() {
        let mut v: CVec<u8, 4> = cvec![1, 2, 3; *; 4];
        v.zeroize();
        assert_eq!(v.len(), 0);
        assert_eq!(
            unsafe { &*slice_from_raw_parts(v.as_ptr(), 4) },
            &[0, 0, 0, 0]
        );
    }

    #[test]
    fn test_fill_remaining() {
        let mut partial: CVec<u8, 4> = cvec![1, 2; *; 4];
        partial.fill_remaining(9);
        assert_eq!(partial.as_slice(), &[1, 2, 9, 9]);

        let mut full: CVec<u8, 2> = cvec![7, 8; *; 2];
        full.fill_remaining(1);
        assert_eq!(full.as_slice(), &[7, 8]);

        let mut zero: CVec<u8, 0> = cvec!();
        zero.fill_remaining(1);
        assert_eq!(zero.as_slice(), &[]);
    }

    #[test]
    fn test_try_as_array() {
        let empty: CVec<u8, 0> = cvec!();
        assert_eq!(empty.try_as_array(), Some(&[]));
        assert_eq!(cvec![1, 2; *; 3].try_as_array(), None);
        assert_eq!(cvec![1, 2, 3; *; 3].try_as_array(), Some(&[1, 2, 3]));
    }

    #[test]
    fn test_try_as_array_mut() {
        let mut empty: CVec<u8, 0> = cvec!();
        assert_eq!(empty.try_as_array_mut().map(|a| *a), Some([]));

        let mut partial: CVec<u8, 3> = cvec![1, 2; *; 3];
        assert_eq!(partial.try_as_array_mut(), None);

        let mut full: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        full.try_as_array_mut().unwrap()[1] = 9;
        assert_eq!(full.as_slice(), &[1, 9, 3]);
    }

    #[test]
    fn test_as_array_unchecked() {
        let full: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        assert_eq!(unsafe { full.as_array_unchecked() }, &[1, 2, 3]);
    }

    #[test]
    fn test_as_array_mut_unchecked() {
        let mut full: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        unsafe { full.as_array_mut_unchecked()[2] = 7 };
        assert_eq!(full.as_slice(), &[1, 2, 7]);
    }

    #[test]
    fn test_into_array_if_full() {
        let empty: CVec<u8, 0> = cvec!();
        assert_eq!(empty.into_array_if_full(), Some([]));
        assert_eq!(cvec![1, 2; *; 3].into_array_if_full(), None);
        assert_eq!(cvec![1, 2, 3; *; 3].into_array_if_full(), Some([1, 2, 3]));
    }

    #[test]
    fn test_to_array_fill_empty() {
        assert_eq!(cvec![; *; 0].to_array_fill_empty(9), []);
        assert_eq!(cvec![1, 2; *; 4].to_array_fill_empty(7), [1, 2, 7, 7]);
        assert_eq!(cvec![1, 2, 3; *; 3].to_array_fill_empty(9), [1, 2, 3]);
    }

    #[test]
    fn test_into_array_unchecked() {
        let full: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        assert_eq!(unsafe { full.into_array_unchecked() }, [1, 2, 3]);
    }

    #[test]
    fn test_into_array_or_panic() {
        let empty: CVec<u8, 0> = cvec!();
        assert_eq!(empty.into_array_or_panic(), []);
        assert_eq!(cvec![1, 2, 3; *; 3].into_array_or_panic(), [1, 2, 3]);
        assert_panics(|| {
            let _ = cvec![1, 2; *; 3].into_array_or_panic();
        });
    }

    #[test]
    fn test_new() {
        let zero = CVec::<u8, 0>::new();
        let regular = CVec::<u8, 4>::new();
        assert_eq!(zero.as_slice(), &[]);
        assert_eq!(regular.as_slice(), &[]);
        assert_eq!(regular.remaining_capacity(), 4);
    }

    #[test]
    fn test_get() {
        let v: CVec<u8, 3> = cvec![1, 2; *; 3];
        assert_eq!(v.get(0), Some(&1));
        assert_eq!(v.get(1), Some(&2));
        assert_eq!(v.get(2), None);
        let empty: CVec<u8, 0> = cvec!();
        assert_eq!(empty.get(0), None);
    }

    #[test]
    fn test_get_mut() {
        let mut v: CVec<u8, 3> = cvec![1, 2; *; 3];
        *v.get_mut(1).unwrap() = 9;
        assert_eq!(v.get_mut(2), None);
        assert_eq!(v.as_slice(), &[1, 9]);
    }

    #[test]
    fn test_get_read() {
        let v: CVec<u8, 3> = cvec![1, 2; *; 3];
        assert_eq!(v.get_read(0), Some(1));
        assert_eq!(v.get_read(1), Some(2));
        assert_eq!(v.get_read(2), None);
    }

    #[test]
    fn test_get_unchecked() {
        let v: CVec<u8, 2> = cvec![4, 5; *; 2];
        assert_eq!(unsafe { *v.get_unchecked(1) }, 5);
    }

    #[test]
    fn test_get_unchecked_mut() {
        let mut v: CVec<u8, 2> = cvec![4, 5; *; 2];
        unsafe { *v.get_unchecked_mut(0) = 9 };
        assert_eq!(v.as_slice(), &[9, 5]);
    }

    #[test]
    fn test_get_unchecked_read() {
        let v: CVec<u8, 2> = cvec![4, 5; *; 2];
        assert_eq!(unsafe { v.get_unchecked_read(0) }, 4);
    }

    #[test]
    fn test_push_or_panic() {
        let mut v = CVec::<u8, 1>::new();
        v.push_or_panic(1);
        assert_eq!(v.as_slice(), &[1]);
        assert_panics(|| v.push_or_panic(2));
    }

    #[test]
    fn test_push_mut_or_panic() {
        let mut v = CVec::<u8, 1>::new();
        *v.push_mut_or_panic(1) = 9;
        assert_eq!(v.as_slice(), &[9]);
        assert_panics(|| {
            let _ = v.push_mut_or_panic(2);
        });
    }

    #[test]
    fn test_push_within_capacity() {
        let mut zero = CVec::<u8, 0>::new();
        assert_eq!(zero.push_within_capacity(1), Err(1));

        let mut v = CVec::<u8, 2>::new();
        assert_eq!(v.push_within_capacity(1), Ok(()));
        assert_eq!(v.push_within_capacity(2), Ok(()));
        assert_eq!(v.push_within_capacity(3), Err(3));
        assert_eq!(v.as_slice(), &[1, 2]);
    }

    #[test]
    fn test_push_unchecked() {
        let mut v = CVec::<u8, 3>::new();
        unsafe {
            v.push_unchecked(1);
            v.push_unchecked(2);
            v.push_unchecked(3);
        }
        assert_eq!(v.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn test_push_front_within_capacity() {
        let mut zero = CVec::<u8, 0>::new();
        assert_eq!(zero.push_front_within_capacity(1), Err(1));

        let mut v: CVec<u8, 3> = cvec![2, 3; *; 3];
        assert_eq!(v.push_front_within_capacity(1), Ok(()));
        assert_eq!(v.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn test_insert_within_capacity() {
        let mut v: CVec<u8, 4> = cvec![1, 3; *; 4];
        assert_eq!(v.insert_within_capacity(1, 2), Ok(()));
        assert_eq!(v.insert_within_capacity(3, 4), Ok(()));
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
        assert_eq!(v.insert_within_capacity(5, 9), Err(9));
        assert_eq!(CVec::<u8, 0>::new().insert_within_capacity(0, 9), Err(9));
    }

    #[test]
    fn test_insert_slice_within_capacity() {
        let mut v: CVec<u8, 6> = cvec![0, 1, 4, 5; *; 6];
        assert_eq!(v.insert_slice_within_capacity(2, &[2, 3]), Ok(()));
        assert_eq!(v.as_slice(), &[0, 1, 2, 3, 4, 5]);

        let mut no_op: CVec<u8, 3> = cvec![1; *; 3];
        assert_eq!(no_op.insert_slice_within_capacity(0, &[]), Ok(()));

        let mut oob: CVec<u8, 3> = cvec![1; *; 3];
        assert_eq!(
            oob.insert_slice_within_capacity(5, &[2]),
            Err(InsertionErr::OutOfBounds { by: 4 })
        );

        let mut full: CVec<u8, 3> = cvec![1, 2; *; 3];
        assert_eq!(
            full.insert_slice_within_capacity(1, &[9, 9]),
            Err(InsertionErr::NotEnoughSpace {
                additional_space_needed: 1
            })
        );
    }

    #[test]
    fn test_push_slice_within_capacity() {
        let mut zero = CVec::<u8, 0>::new();
        assert_eq!(zero.push_slice_within_capacity(&[]), Ok(()));
        assert_eq!(
            zero.push_slice_within_capacity(&[1]),
            Err(InsertionErr::NotEnoughSpace {
                additional_space_needed: 1
            })
        );

        let mut v: CVec<u8, 4> = cvec![1, 2; *; 4];
        assert_eq!(v.push_slice_within_capacity(&[3, 4]), Ok(()));
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);
    }

    #[test]
    fn test_as_ptr() {
        let v: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        assert_eq!(v.as_ptr(), v.as_slice().as_ptr());
    }

    #[test]
    fn test_as_mut_ptr() {
        let mut v: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        assert_eq!(v.as_mut_ptr(), v.as_mut_slice().as_mut_ptr());
    }

    #[test]
    fn test_as_slice() {
        let empty: CVec<u8, 0> = cvec!();
        assert_eq!(empty.as_slice(), &[]);
        assert_eq!(cvec![1, 2; *; 3].as_slice(), &[1, 2]);
    }

    #[test]
    fn test_as_mut_slice() {
        let mut v: CVec<u8, 3> = cvec![1, 2; *; 3];
        v.as_mut_slice()[1] = 9;
        assert_eq!(v.as_slice(), &[1, 9]);
    }

    #[test]
    fn test_try_append_slice() {
        let mut zero = CVec::<u8, 0>::new();
        assert_eq!(zero.try_append_slice(&[]), Ok(()));
        assert_eq!(zero.try_append_slice(&[1]), Err(&[][..]));

        let mut v: CVec<u8, 3> = cvec![1; *; 3];
        assert_eq!(v.try_append_slice(&[2, 3]), Ok(()));
        assert_eq!(v.as_slice(), &[1, 2, 3]);

        let mut limited: CVec<u8, 3> = cvec![1; *; 3];
        assert_eq!(limited.try_append_slice(&[2, 3, 4]), Err(&[2, 3][..]));
    }

    #[test]
    fn test_append_slice_or_crop() {
        let mut zero = CVec::<u8, 0>::new();
        assert_eq!(zero.append_slice_or_crop(&[]), None);
        assert_eq!(zero.append_slice_or_crop(&[1]), Some(&[1][..]));

        let mut v: CVec<u8, 4> = cvec![1; *; 4];
        assert_eq!(v.append_slice_or_crop(&[2, 3, 4]), None);
        assert_eq!(v.as_slice(), &[1, 2, 3, 4]);

        let mut cropped: CVec<u8, 4> = cvec![1; *; 4];
        assert_eq!(cropped.append_slice_or_crop(&[2, 3, 4, 5]), Some(&[5][..]));
        assert_eq!(cropped.as_slice(), &[1, 2, 3, 4]);
    }

    #[test]
    fn test_append_slice_or_panic() {
        let mut v: CVec<u8, 3> = cvec![1; *; 3];
        v.append_slice_or_panic(&[2, 3]);
        assert_eq!(v.as_slice(), &[1, 2, 3]);
        assert_panics(|| {
            let mut full: CVec<u8, 2> = cvec![1; *; 2];
            full.append_slice_or_panic(&[2, 3]);
        });
    }

    #[test]
    fn test_append_slice_unchecked() {
        let mut v: CVec<u8, 3> = cvec![1; *; 3];
        unsafe { v.append_slice_unchecked(&[2, 3]) };
        assert_eq!(v.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn test_from_slice_or_panic() {
        assert_eq!(CVec::<u8, 0>::from_slice_or_panic(&[]).as_slice(), &[]);
        assert_eq!(
            CVec::<u8, 3>::from_slice_or_panic(&[1, 2, 3]).as_slice(),
            &[1, 2, 3]
        );
        assert_panics(|| {
            let _ = CVec::<u8, 2>::from_slice_or_panic(&[1, 2, 3]);
        });
    }

    #[test]
    fn test_from_slice_unchecked() {
        let v = unsafe { CVec::<u8, 3>::from_slice_unchecked(&[1, 2, 3]) };
        assert_eq!(v.as_slice(), &[1, 2, 3]);
    }

    #[test]
    fn test_from_slice_or_crop() {
        assert_eq!(CVec::<u8, 0>::from_slice_or_crop(&[1, 2]).as_slice(), &[]);
        assert_eq!(
            CVec::<u8, 3>::from_slice_or_crop(&[1, 2, 3, 4]).as_slice(),
            &[1, 2, 3]
        );
        assert_eq!(CVec::<u8, 3>::from_slice_or_crop(&[1]).as_slice(), &[1]);
    }

    #[test]
    fn test_retain() {
        let mut v: CVec<u8, 5> = cvec![1, 2, 3, 4; *; 5];
        v.retain(|n| n % 2 == 0);
        assert_eq!(v.as_slice(), &[2, 4]);

        let mut none: CVec<u8, 3> = cvec![1, 3; *; 3];
        none.retain(|_| false);
        assert_eq!(none.as_slice(), &[]);
    }

    #[test]
    fn test_retain_mut() {
        let mut v: CVec<u8, 5> = cvec![1, 2, 3, 4; *; 5];
        v.retain_mut(|n| {
            *n += 1;
            *n % 2 == 0
        });
        assert_eq!(v.as_slice(), &[2, 4]);
    }

    #[test]
    fn test_remaining_capacity() {
        let empty: CVec<u8, 0> = cvec!();
        let regular: CVec<u8, 4> = cvec![; *; 4];
        assert_eq!(empty.remaining_capacity(), 0);
        assert_eq!(regular.remaining_capacity(), 4);
        assert_eq!(cvec![1, 2; *; 4].remaining_capacity(), 2);
    }

    #[test]
    fn test_from_array_as_full() {
        assert_eq!(CVec::<u8, 0>::from_array_as_full(&[]).as_slice(), &[]);
        assert_eq!(
            CVec::<u8, 3>::from_array_as_full(&[1, 2, 3]).as_slice(),
            &[1, 2, 3]
        );
    }

    #[test]
    fn test_pop() {
        let mut empty: CVec<u8, 0> = cvec![];
        assert_eq!(empty.pop(), None);

        let mut v: CVec<u8, 2> = cvec![1, 2; *; 2];
        assert_eq!(v.pop(), Some(2));
        assert_eq!(v.pop(), Some(1));
        assert_eq!(v.pop(), None);
    }

    #[test]
    fn test_pop_front() {
        let mut empty = CVec::<u8, 0>::new();
        assert_eq!(empty.pop_front(), None);

        let mut v: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        assert_eq!(v.pop_front(), Some(1));
        assert_eq!(v.pop_front(), Some(2));
        assert_eq!(v.pop_front(), Some(3));
        assert_eq!(v.pop_front(), None);
    }

    #[test]
    fn test_pop_at() {
        let mut v: CVec<u8, 4> = cvec![1, 2, 3; *; 4];
        assert_eq!(v.pop_at(0), Some(1));
        assert_eq!(v.pop_at(1), Some(3));
        assert_eq!(v.pop_at(1), None);
        assert_eq!(v.pop_at(0), Some(2));
        assert_eq!(v.pop_at(0), None);
    }

    #[test]
    fn test_remove_range() {
        let mut prefix: CVec<u8, 5> = cvec![0, 1, 2, 3, 4; *; 5];
        prefix.remove_range(..2);
        assert_eq!(prefix.as_slice(), &[2, 3, 4]);

        let mut suffix: CVec<u8, 5> = cvec![0, 1, 2, 3, 4; *; 5];
        suffix.remove_range(3..);
        assert_eq!(suffix.as_slice(), &[0, 1, 2]);

        let mut bounded: CVec<u8, 6> = cvec![0, 1, 2, 3, 4, 5; *; 6];
        bounded.remove_range(2..4);
        assert_eq!(bounded.as_slice(), &[0, 1, 4, 5]);

        let mut bounded_inclusive: CVec<u8, 6> = cvec![0, 1, 2, 3, 4, 5; *; 6];
        bounded_inclusive.remove_range(2..=4);
        assert_eq!(bounded_inclusive.as_slice(), &[0, 1, 5]);

        let mut full: CVec<u8, 4> = cvec![0, 1, 2, 3; *; 4];
        full.remove_range(..);
        assert_eq!(full.as_slice(), &[]);

        let mut empty_prefix: CVec<u8, 4> = cvec![0, 1, 2, 3; *; 4];
        empty_prefix.remove_range(..0);
        assert_eq!(empty_prefix.as_slice(), &[0, 1, 2, 3]);

        let mut empty_suffix: CVec<u8, 4> = cvec![0, 1, 2, 3; *; 4];
        empty_suffix.remove_range(4..);
        assert_eq!(empty_suffix.as_slice(), &[0, 1, 2, 3]);

        let mut empty_mid: CVec<u8, 4> = cvec![0, 1, 2, 3; *; 4];
        empty_mid.remove_range(2..2);
        assert_eq!(empty_mid.as_slice(), &[0, 1, 2, 3]);

        assert_panics(|| {
            let mut past_end: CVec<u8, 4> = cvec![0, 1, 2, 3; *; 4];
            past_end.remove_range(..5);
        });

        assert_panics(|| {
            let mut suffix_past_len: CVec<u8, 4> = cvec![0, 1, 2, 3; *; 4];
            suffix_past_len.remove_range(5..);
        });

        assert_panics(|| {
            let mut end_before_start: CVec<u8, 4> = cvec![0, 1, 2, 3; *; 4];
            end_before_start.remove_range(3..2);
        });
    }

    #[test]
    fn test_remove_contiguous_or_panic() {
        let mut v: CVec<u8, 6> = cvec![0, 1, 2, 3, 4, 5; *; 6];
        v.remove_contiguous_or_panic(2, 0);
        assert_eq!(v.as_slice(), &[0, 1, 2, 3, 4, 5]);
        v.remove_contiguous_or_panic(1, 3);
        assert_eq!(v.as_slice(), &[0, 4, 5]);
        v.remove_contiguous_or_panic(1, 2);
        assert_eq!(v.as_slice(), &[0]);
        assert_panics(|| {
            let mut bad: CVec<u8, 2> = cvec![1; *; 2];
            bad.remove_contiguous_or_panic(1, 1);
        });
    }

    #[test]
    fn test_remove() {
        let mut v: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        v.remove(1);
        assert_eq!(v.as_slice(), &[1, 3]);
        v.remove(0);
        assert_eq!(v.as_slice(), &[3]);
        assert_panics(|| {
            let mut bad: CVec<u8, 1> = cvec![1; *; 1];
            bad.remove(1);
        });
    }

    #[test]
    fn test_from_elem() {
        assert_eq!(CVec::<u8, 0>::from_elem(9).as_slice(), &[]);
        assert_eq!(CVec::<u8, 3>::from_elem(9).as_slice(), &[9, 9, 9]);
    }

    #[test]
    fn test_from_elem_up_to_or_panic() {
        assert_eq!(
            CVec::<u8, 3>::from_elem_up_to_or_panic(9, 0).as_slice(),
            &[]
        );
        assert_eq!(
            CVec::<u8, 3>::from_elem_up_to_or_panic(9, 2).as_slice(),
            &[9, 9]
        );
        assert_panics(|| {
            let _ = CVec::<u8, 2>::from_elem_up_to_or_panic(9, 3);
        });
    }

    #[test]
    fn test_map() {
        assert_eq!(CVec::<u8, 0>::new().map(|n| n as u16).as_slice(), &[]);
        assert_eq!(
            CVec::<u8, 3>::from_slice_or_panic(&[1, 2, 3])
                .map(|n| n as u16 * 10)
                .as_slice(),
            &[10, 20, 30]
        );
    }

    #[test]
    fn test_from_str_or_panic() {
        assert_eq!(CVec::<u8, 0>::from_str_or_panic("").as_str(), Ok(""));
        assert_eq!(
            CVec::<u8, 4>::from_str_or_panic("hola").as_str(),
            Ok("hola")
        );
        assert_panics(|| {
            let _ = CVec::<u8, 3>::from_str_or_panic("hola");
        });
    }

    #[test]
    fn test_from_str_or_crop() {
        assert_eq!(CVec::<u8, 0>::from_str_or_crop("hola").as_str(), Ok(""));
        assert_eq!(CVec::<u8, 4>::from_str_or_crop("ábcde").as_str(), Ok("ábc"));
        assert_eq!(CVec::<u8, 8>::from_str_or_crop("hola").as_str(), Ok("hola"));
    }

    #[test]
    fn test_as_str_or_panic() {
        assert_eq!(
            CVec::<u8, 4>::from_str_or_panic("hola").as_str_or_panic(),
            "hola"
        );
        assert_panics(|| {
            let _ = CVec::<u8, 1>::from_slice_or_panic(&[0xff]).as_str_or_panic();
        });
    }

    #[test]
    fn test_as_str() {
        assert_eq!(CVec::<u8, 0>::new().as_str(), Ok(""));
        assert_eq!(
            CVec::<u8, 4>::from_str_or_panic("hola").as_str(),
            Ok("hola")
        );
        assert!(
            CVec::<u8, 1>::from_slice_or_panic(&[0xff])
                .as_str()
                .is_err()
        );
    }

    #[test]
    fn test_as_str_mut() {
        let mut ok = CVec::<u8, 4>::from_str_or_panic("hola");
        ok.as_str_mut().unwrap().make_ascii_uppercase();
        assert_eq!(ok.as_str(), Ok("HOLA"));

        let mut invalid = CVec::<u8, 1>::from_slice_or_panic(&[0xff]);
        assert!(invalid.as_str_mut().is_err());
    }

    #[test]
    fn test_as_str_unchecked() {
        let ok = CVec::<u8, 4>::from_str_or_panic("hola");
        assert_eq!(unsafe { ok.as_str_unchecked() }, "hola");
    }

    #[test]
    fn test_as_str_mut_unchecked() {
        let mut ok = CVec::<u8, 4>::from_str_or_panic("hola");
        unsafe { ok.as_str_mut_unchecked().make_ascii_uppercase() };
        assert_eq!(ok.as_str(), Ok("HOLA"));
    }

    #[test]
    fn test_push_str_or_panic() {
        let mut v = CVec::<u8, 4>::new();
        v.push_str_or_panic("hola");
        assert_eq!(v.as_str(), Ok("hola"));
        assert_panics(|| {
            let mut short = CVec::<u8, 3>::new();
            short.push_str_or_panic("hola");
        });
    }

    #[test]
    fn test_push_str_unchecked() {
        let mut v = CVec::<u8, 4>::new();
        unsafe { v.push_str_unchecked("hola") };
        assert_eq!(v.as_str(), Ok("hola"));
    }

    #[test]
    fn test_try_push_str() {
        let mut zero = CVec::<u8, 0>::new();
        assert_eq!(zero.try_push_str("a"), Err(("", "a")));

        let mut v = CVec::<u8, 8>::from_str_or_panic("hola");
        assert_eq!(v.try_push_str("ab"), Ok(()));
        assert_eq!(v.as_str(), Ok("holaab"));

        let mut limited = CVec::<u8, 6>::from_str_or_panic("hola");
        assert_eq!(limited.try_push_str("ñ!"), Err(("ñ", "!")));
        assert_eq!(limited.as_str(), Ok("hola"));
    }

    #[test]
    fn test_push_str_or_crop() {
        let mut zero = CVec::<u8, 0>::new();
        assert_eq!(zero.push_str_or_crop("hola"), Some("hola"));

        let mut v = CVec::<u8, 8>::from_str_or_panic("hola");
        assert_eq!(v.push_str_or_crop("MUNDO"), Some("O"));
        assert_eq!(v.as_str(), Ok("holaMUND"));
    }

    #[test]
    fn test_push_char_if_possible() {
        let mut v = CVec::<u8, 4>::from_str_or_panic("ab");
        assert_eq!(v.push_char_if_possible('ñ'), Ok(2));
        assert_eq!(v.as_str(), Ok("abñ"));
        assert_eq!(v.push_char_if_possible('!'), Err(1));

        let mut zero = CVec::<u8, 0>::new();
        assert_eq!(zero.push_char_if_possible('a'), Err(1));
    }

    #[test]
    fn test_size_of() {
        assert_eq!(size_of::<CVec8<u8, 3>>(), 4);
        assert_eq!(
            size_of::<CVec8<u8, { u8::MAX as usize }>>(),
            u8::MAX as usize + 1
        );
        assert_eq!(size_of::<CVec16<u8, 3>>(), 6);
    }

    #[test]
    fn test_trait_impls_and_fmt_write() {
        let v: CVec<u8, 3> = cvec![1, 2, 3; *; 3];
        let cloned = v.clone();
        let copied = v;
        let collected: Vec<_> = copied.into_iter().collect();
        let borrowed: Vec<_> = (&cloned).into_iter().copied().collect();

        assert_eq!(cloned, copied);
        assert_eq!(collected, vec![1, 2, 3]);
        assert_eq!(borrowed, vec![1, 2, 3]);
        assert_eq!(CVec::<u8, 2>::default().as_slice(), &[]);

        let mut writer = CVec::<u8, 6>::new();
        write!(&mut writer, "abc{}", 'd').unwrap();
        assert_eq!(writer.as_str(), Ok("abcd"));
    }

    #[test]
    #[should_panic(expected = "iterator contains more than 3 elements")]
    fn test_from_iter_out_of_bounds() {
        let iter = [1, 2, 3, 4].into_iter();
        let _: CVec<i32, 3> = CVec::from_iter(iter);
    }
}
