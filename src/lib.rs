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

            /// Returns true if `len == N`.
            #[inline]
            pub const fn is_full(&self) -> bool {
                self.len() == N
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

            /// Panics if N
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
                if self.len() < N {
                    // SAFETY: we just confirmed we got room
                    unsafe {
                        self.buf
                            .as_mut_ptr()
                            .add(self.len())
                            .write(MaybeUninit::new(element))
                    };
                    self.len += 1;
                    Ok(())
                } else {
                    Err(element)
                }
            }

            /// Returns an Err with the element if already full
            #[inline]
            pub const fn push_front_within_capacity(&mut self, element: T) -> Result<(), T> {
                self.insert_within_capacity(0, element)
            }

            /// Returns an Err with the element if already full
            #[inline]
            pub const fn insert_within_capacity(&mut self, at: usize, element: T) -> Result<(), T> {
                if self.len() == N {
                    return Err(element)
                }
                if self.len() < at { // out of bounds
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
                if self.len() < index {
                    return None
                }
                let ret = unsafe{ self.get_unchecked_read(index) };
                self.remove(index);
                Some(ret)
            }

            #[inline]
            pub fn remove_range<R: RangeBounds<usize>>(&mut self, range: R) {
                use Bound::*;
                let start = match range.start_bound() {
                    Included(n) => *n,
                    Excluded(n) => *n + 1,
                    Unbounded => 0,
                };
                let end = match range.end_bound() {
                    Included(n) => *n,
                    Excluded(n) => *n - 1,
                    Unbounded => self.len(),
                };
                self.remove_contiguous_or_panic(start, end - start);
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CVec;
    use crate::cvec::cvec;
    use crate::cvec8::cvec8;
    use std::ptr::slice_from_raw_parts;

    #[test]
    fn test_size_of() {
        assert_eq!(size_of::<CVec8<u8, 3>>(), 4);
        assert_eq!(
            size_of::<CVec8<u8, { u8::MAX as usize }>>(),
            u8::MAX as usize + 1
        );
        assert_eq!(size_of::<CVec16<u8, 3>>(), 6); // 3 bytes + 1 alignment byte + 2 bytes for index
    }

    #[test]
    fn testit() -> Result<(), usize> {
        let mut v: Vec<u8> = vec![];
        let mut m: CVec8<u8, 255> = CVec8::new();

        v.push(2);

        m.push_or_panic(2);
        v.push(3);
        m.push_or_panic(3);

        assert_eq!(m.as_slice(), &[2, 3]);

        assert_eq!(m.as_slice(), &v);

        assert_eq!(m[0], v[0]);
        assert_eq!(m[0..2], v[0..2]);

        v.extend(&[3, 4]);
        m.extend(&[3, 4]);

        assert_eq!(m[..], v[..]);
        m.append_slice_or_panic(&[2, 3]);

        assert_eq!(m.as_slice(), &[2, 3, 3, 4, 2, 3]);

        m.retain(|&x| x % 2 == 0);
        v.retain(|&x| x % 2 == 0);

        assert_eq!(m.as_slice(), &[2, 4, 2]);
        Ok(())
    }

    #[test]
    fn test_into_array() {
        let s = vec![0; 3];
        let cvec = cvec![0, 1, 2; *; 6];
        assert_eq!(cvec, [0, 1, 2]);
        let arr = cvec.to_array_fill_empty(3);
        assert_eq!(cvec, [0, 1, 2]);
        assert_eq!(arr, [0, 1, 2, 3, 3, 3])
    }

    #[test]
    fn test_try_append_slice() {
        let mut cvec = CVec::<u8, 3>::from_slice_or_panic(&[1]);
        let part_that_fits = cvec
            .try_append_slice(&[2, 3, 4])
            .expect_err("should fail due to lack of space");
        assert_eq!(part_that_fits, [2, 3]);
        let result = cvec.try_append_slice(part_that_fits);
        assert!(result.is_ok());
        assert_eq!(cvec, [1, 2, 3]);
    }

    #[test]
    fn test_remove_contiguous() {
        let mut cvec = cvec!(0, 1, 2, 3, 4, 5, 6, 7, 8, 9; *; *);
        cvec.remove_contiguous_or_panic(1, 5);
        assert_eq!(cvec, [0, 6, 7, 8, 9]);

        cvec.remove_contiguous_or_panic(1, 4);
        assert_eq!(cvec, [0])
    }

    #[test]
    fn test_remove_range() {
        const STR: &str = "I can't believe...NOT!!!! it's NOT HEAP!";
        const REMOVE: &str = "...NOT!!!!";
        let mut cvec = CVec::<u8, 255>::from_slice_or_panic(STR.as_bytes());

        let start = STR.find(REMOVE).unwrap();
        let count = REMOVE.len();
        cvec.remove_contiguous_or_panic(start, count);

        let result: &str = str::from_utf8(cvec.as_slice()).unwrap();
        assert_eq!(
            result, "I can't believe it's NOT HEAP!",
            "range correclty removed"
        );

        let original_slice =
            str::from_utf8(unsafe { &*slice_from_raw_parts(cvec.as_ptr(), STR.len()) }).unwrap();
        assert_eq!(
            original_slice, "I can't believe it's NOT HEAP! NOT HEAP!",
            "freed memory left untouched"
        )
    }

    #[test]
    fn test_remove_range_at_the_end() {
        const STR: &str = "I can't believe it's NOT HEAP!...NOT!!!!";
        const REMOVE: &str = "...NOT!!!!";
        let mut cvec = CVec::<u8, 255>::from_slice_or_panic(STR.as_bytes());

        let start = STR.find(REMOVE).unwrap();
        let count = REMOVE.len();
        cvec.remove_contiguous_or_panic(start, count);

        let result: &str = str::from_utf8(cvec.as_slice()).unwrap();
        assert_eq!(
            result, "I can't believe it's NOT HEAP!",
            "range correclty removed"
        );

        let original_slice =
            str::from_utf8(unsafe { &*slice_from_raw_parts(cvec.as_ptr(), STR.len()) }).unwrap();
        assert_eq!(
            original_slice, "I can't believe it's NOT HEAP!...NOT!!!!",
            "freed memory left untouched"
        )
    }

    #[test]
    fn test_insertion() {
        let mut cvec = cvec8!(0,1,4,5; *; 6);
        cvec.insert_slice_within_capacity(2, &[2, 3]).unwrap();
        assert_eq!(cvec.as_slice(), &[0, 1, 2, 3, 4, 5]);

        let mut cvec = cvec8!(0,1,4,5; *; 6);
        let res = cvec.insert_slice_within_capacity(2, &[2, 3, 4]);
        assert_eq!(cvec.as_slice(), &[0, 1, 4, 5]);
        assert_eq!(
            res,
            Err(InsertionErr::NotEnoughSpace {
                additional_space_needed: 1
            })
        );

        let mut cvec = cvec8!(0,1,4,5; *; 6);
        let res = cvec.insert_slice_within_capacity(10, &[2, 3]);
        assert_eq!(cvec.as_slice(), &[0, 1, 4, 5]);
        assert_eq!(res, Err(InsertionErr::OutOfBounds { by: 6 }));

        let mut cvec = cvec8!(0,1,4,5; *; 6);
        // insert at the end
        cvec.insert_slice_within_capacity(4, &[2, 3]).unwrap();
        assert_eq!(cvec.as_slice(), &[0, 1, 4, 5, 2, 3]);

        let mut cvec = cvec8!(0,1,4,5; *; 6);
        let res = cvec.insert_slice_within_capacity(10, &[2, 3, 4]);
        assert_eq!(cvec.as_slice(), &[0, 1, 4, 5]);
        assert_eq!(res, Err(InsertionErr::OutOfBounds { by: 6 }));

        let mut cvec = cvec8!(0,1,4,5; *; 6);
        // insert at the beginning
        cvec.insert_slice_within_capacity(0, &[2, 3]).unwrap();
        assert_eq!(cvec.as_slice(), &[2, 3, 0, 1, 4, 5]);
    }

    #[test]
    fn test_macro() {
        // Set v to a `CVec<char, 5>` that is empty:
        let v: CVec<char, 5> = cvec!();
        assert_eq!(v, []);
        // Set v to a CVec<char, 5> that is empty:
        let v: CVec<char, _> = cvec![; *; 5];
        assert_eq!(v, []);
        assert_eq!(v.remaining_capacity(), 5);

        // Set v to a CVec<char, 5> with 'a' repeated 5 times:
        let v: CVec<char, 5> = cvec!['a'; _; _];
        assert_eq!(v, ['a', 'a', 'a', 'a', 'a']);
        // Set v to a CVec<char, 5> with 'a' repeated 5 times:
        let v = cvec!['a'; _; 5];
        assert_eq!(v, ['a', 'a', 'a', 'a', 'a']);
        // Set v to a CVec<char, 5> with 1 element, 'a':
        let v: CVec<char, 5> = cvec!['a'; *; _];
        assert_eq!(v, ['a']);
        // Set v to a CVec<char, 5> with 2 elements, 'a', and 'b':
        let v = cvec!['a', 'b'; *; 5];
        assert_eq!(v, ['a', 'b']);
        // Set v to a CVec<char, 5> with 3 elements, 'a', 'a', and 'a':
        let v: CVec<_, 5> = cvec!['a'; 3; _];
        assert_eq!(v, ['a', 'a', 'a']);
        // Set v to a CVec<char, 5> with 3 elements, 'a', 'a', and 'a':
        let v = cvec!['a'; 3; 5];
        assert_eq!(v, ['a', 'a', 'a']);
        // Set v to a CVec<char, 5> with 5 elements, 'a', 'b', 'c', 'd', 'e':
        let v = cvec!['a', 'b', 'c', 'd', 'e'; *; *];
        assert_eq!(v, ['a', 'b', 'c', 'd', 'e']);
    }

    #[test]
    fn test_macro_lentype_u8() {
        // Set v to a `CVec<char, 5>` that is empty:
        let v: CVec8<char, 5> = cvec8!();
        assert_eq!(v, []);
        // Set v to a CVec<char, 5> that is empty:
        let v: CVec8<char, _> = cvec8![; *; 5];
        assert_eq!(v, []);
        assert_eq!(v.remaining_capacity(), 5);

        // Set v to a CVec<char, 5> with 'a' repeated 5 times:
        let v: CVec8<char, 5> = cvec8!['a'; _; _];
        assert_eq!(v, ['a', 'a', 'a', 'a', 'a']);
        // Set v to a CVec<char, 5> with 'a' repeated 5 times:
        let v = cvec8!['a'; _; 5];
        assert_eq!(v, ['a', 'a', 'a', 'a', 'a']);
        // Set v to a CVec<char, 5> with 1 element, 'a':
        let v: CVec8<char, 5> = cvec8!['a'; *; _];
        assert_eq!(v, ['a']);
        // Set v to a CVec<char, 5> with 2 elements, 'a', and 'b':
        let v = cvec8!['a', 'b'; *; 5];
        assert_eq!(v, ['a', 'b']);
        // Set v to a CVec<char, 5> with 3 elements, 'a', 'a', and 'a':
        let v: CVec8<_, 5> = cvec8!['a'; 3; _];
        assert_eq!(v, ['a', 'a', 'a']);
        // Set v to a CVec<char, 5> with 3 elements, 'a', 'a', and 'a':
        let v = cvec8!['a'; 3; 5];
        assert_eq!(v, ['a', 'a', 'a']);
        // Set v to a CVec<char, 5> with 5 elements, 'a', 'b', 'c', 'd', 'e':
        let v = cvec8!['a', 'b', 'c', 'd', 'e'; *; *];
        assert_eq!(v, ['a', 'b', 'c', 'd', 'e']);
    }

    #[test]
    fn test_str() {
        const MSG: &str = "hola CAPO yo soy santi";
        const LEN: usize = MSG.len();
        let mut v: CVec<u8, LEN> = cvec!();
        v.push_str_or_panic(MSG);
        assert_eq!(v, MSG);

        const SANTI: &str = "santi";
        v.remove_contiguous_or_panic(
            unsafe { v.as_str_unchecked() }.find(SANTI).unwrap(),
            SANTI.len(),
        );

        assert_eq!(v, "hola CAPO yo soy ");

        let (fits, fits_not) = v.try_push_str("san👍tiago").unwrap_err();

        assert_eq!((fits, fits_not), ("san", "👍tiago"));

        v.push_str_or_panic(fits);

        assert_eq!(v, "hola CAPO yo soy san");

        assert_eq!(v.try_push_str("👍tiago").unwrap_err(), ("", "👍tiago"))
    }

    #[test]
    fn test_get() {
        let mut v: CVec<u8, 5> = cvec!(1,2,3; *; _);
        assert_eq!(Some(&1), v.get(0));
        assert_eq!(Some(&2), v.get(1));
        assert_eq!(Some(&3), v.get(2));
        assert_eq!(None, v.get(3));
        assert_eq!(None, v.get(4));
        assert_eq!(None, v.get(5));
        assert_eq!(None, v.get(6));

        assert_eq!(Some(1), v.get_read(0));
        assert_eq!(Some(2), v.get_read(1));
        assert_eq!(Some(3), v.get_read(2));
        assert_eq!(None, v.get_read(3));
        assert_eq!(None, v.get_read(4));
        assert_eq!(None, v.get_read(5));
        assert_eq!(None, v.get_read(6));

        assert_eq!(Some(&mut 1), v.get_mut(0));
        assert_eq!(Some(&mut 2), v.get_mut(1));
        assert_eq!(Some(&mut 3), v.get_mut(2));
        assert_eq!(None, v.get_mut(3));
        assert_eq!(None, v.get_mut(4));
        assert_eq!(None, v.get_mut(5));
        assert_eq!(None, v.get_mut(6));
    }


    #[test]
    fn test_pop_at() {
        let mut v: CVec<u8, 5> = cvec!(1,2,3; *; _);
        assert_eq!(Some(1), v.pop_at(0));
        assert_eq!(Some(3), v.pop_at(1));
        assert_eq!(None, v.pop_at(2));
        assert_eq!(Some(2), v.pop_at(0));
        assert_eq!(0, v.len());
    }


}

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
