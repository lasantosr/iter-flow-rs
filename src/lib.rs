#![no_std]

//! Extra iterator methods.
//!
//! To extend [`Iterator`] with methods in this crate, import the [`Iterflow`] trait:
//!
//! ```
//! use iter_flow::Iterflow;
//! ```
//!
//! Now, new methods like [`and_then`](Iterflow::and_then) are available on all Result's iterators:
//!
//! ```
//! # use iter_flow::Iterflow;
//! let it = (0..4)
//!     .map(|n| if n == 0 { Err("invalid!") } else { Ok(n - 1) })
//!     .and_then(|n| if n > 0 { Ok(n - 1) } else { Err("illegal!") })
//!     .map_ok(|n| (n + 1) * 2)
//!     .flat_map_ok(|n| (0..n));
//!
//! iter_flow::assert_equal(
//!     it,
//!     vec![
//!         Err("invalid!"),
//!         Err("illegal!"),
//!         Ok(0),
//!         Ok(1),
//!         Ok(0),
//!         Ok(1),
//!         Ok(2),
//!         Ok(3),
//!     ],
//! );
//! ```

#[cfg(feature = "use_alloc")]
extern crate alloc;

#[cfg(feature = "use_alloc")]
use alloc::vec::Vec;
use core::fmt;

/// The concrete iterator types.
pub mod structs {
    pub use crate::{
        and_then::{AndThen, AndThenBorrow},
        flatten::FlattenOk,
        map_err::MapErr,
        map_ok::{MapOk, MapOkBorrow},
    };
}

mod and_then;
mod flatten;
mod map_err;
mod map_ok;

/// An [`Iterator`] blanket implementation that provides extra adaptors and
/// methods.
pub trait Iterflow: Iterator {
    /// Return an iterator adaptor that applies the provided closure to every `Result::Err` value. `Result::Ok` values
    /// are unchanged.
    ///
    /// ```
    /// use iter_flow::Iterflow;
    ///
    /// let input = vec![Ok(41), Err(false), Err(true)];
    /// let it = input.into_iter().map_err(|b| !b);
    /// iter_flow::assert_equal(it, vec![Ok(41), Err(true), Err(false)]);
    /// ```
    fn map_err<F, T, E, R>(self, op: F) -> map_err::MapErr<Self, F>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        F: FnMut(E) -> R,
    {
        map_err::map_err(self, op)
    }

    /// Return an iterator adaptor that applies the provided closure to every `Result::Ok` value. `Result::Err` values
    /// are unchanged.
    ///
    /// ```
    /// use iter_flow::Iterflow;
    ///
    /// let input = vec![Ok(41), Err(false), Ok(11)];
    /// let it = input.into_iter().map_ok(|i| i + 1);
    /// iter_flow::assert_equal(it, vec![Ok(42), Err(false), Ok(12)]);
    /// ```
    fn map_ok<F, T, U, E>(self, op: F) -> map_ok::MapOk<Self, F>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        F: FnMut(T) -> U,
    {
        map_ok::map_ok(self, op)
    }

    /// Return an iterator adaptor that applies the provided closure to every `Result::Ok` value. `Result::Err` values
    /// are unchanged.
    ///
    /// ```
    /// use iter_flow::Iterflow;
    ///
    /// let input = vec![Ok(41), Err(false), Ok(11)];
    /// let it = input.into_iter().map_ok_borrow(|i: &i32| i + 1);
    /// iter_flow::assert_equal(it, vec![Ok(42), Err(false), Ok(12)]);
    /// ```
    fn map_ok_borrow<F, T, U, E>(self, op: F) -> map_ok::MapOkBorrow<Self, F>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        F: FnMut(&T) -> U,
    {
        map_ok::map_ok_borrow(self, op)
    }

    /// Return an iterator adaptor that applies the provided fallible closure to every `Result::Ok` value. `Result::Err`
    /// values are unchanged.
    ///
    /// ```
    /// use iter_flow::Iterflow;
    ///
    /// let input = vec![Ok(0), Err(false), Ok(11)];
    /// let it = input
    ///     .into_iter()
    ///     .and_then(|i| if i == 0 { Err(false) } else { Ok(i - 1) });
    /// iter_flow::assert_equal(it, vec![Err(false), Err(false), Ok(10)]);
    /// ```
    fn and_then<F, T, U, E, R>(self, op: F) -> and_then::AndThen<Self, F>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        F: FnMut(T) -> Result<U, R>,
        E: From<R>,
    {
        and_then::and_then(self, op)
    }

    /// Return an iterator adaptor that applies the provided fallible closure to every `Result::Ok` value. `Result::Err`
    /// values are unchanged.
    ///
    /// ```
    /// use iter_flow::Iterflow;
    ///
    /// let input = vec![Ok(0), Err(false), Ok(11)];
    /// let it = input
    ///     .into_iter()
    ///     .and_then_borrow(|i: &i32| if i == &0 { Err(false) } else { Ok(i - 1) });
    /// iter_flow::assert_equal(it, vec![Err(false), Err(false), Ok(10)]);
    /// ```
    fn and_then_borrow<F, T, U, E, R>(self, op: F) -> and_then::AndThenBorrow<Self, F>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        F: FnMut(&T) -> Result<U, R>,
        E: From<R>,
    {
        and_then::and_then_borrow(self, op)
    }

    /// Return an iterator adaptor that applies the provided closure to every `Result::Ok` value and then flattens it.
    /// `Result::Err` values are unchanged.
    ///
    /// ```
    /// use iter_flow::Iterflow;
    ///
    /// let input = vec![Ok(41), Err(false), Ok(11)];
    /// let it = input.into_iter().flat_map_ok(|i| (i..=(i + 1)));
    /// iter_flow::assert_equal(it, vec![Ok(41), Ok(42), Err(false), Ok(11), Ok(12)]);
    /// ```
    fn flat_map_ok<F, T, U, E>(self, op: F) -> flatten::FlattenOk<map_ok::MapOk<Self, F>, U, E>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        F: FnMut(T) -> U,
        U: IntoIterator,
    {
        flatten::flat_map_ok(self, op)
    }

    /// Return an iterator adaptor that applies the provided closure to every `Result::Ok` value and then flattens it.
    /// `Result::Err` values are unchanged.
    ///
    /// ```
    /// use iter_flow::Iterflow;
    ///
    /// let input = vec![Ok(41), Err(false), Ok(11)];
    /// let it = input
    ///     .into_iter()
    ///     .flat_map_ok_borrow(|i: &i32| (*i..=(*i + 1)));
    /// iter_flow::assert_equal(it, vec![Ok(41), Ok(42), Err(false), Ok(11), Ok(12)]);
    /// ```
    fn flat_map_ok_borrow<F, T, U, E>(self, op: F) -> flatten::FlattenOk<map_ok::MapOkBorrow<Self, F>, U, E>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        F: FnMut(&T) -> U,
        U: IntoIterator,
    {
        flatten::flat_map_ok_borrow(self, op)
    }

    /// Return an iterator adaptor that applies the provided fallible closure to every `Result::Ok` value and then
    /// flattens it. `Result::Err` values are unchanged.
    ///
    /// ```
    /// use iter_flow::Iterflow;
    ///
    /// let input = vec![Ok(0), Err(false), Ok(11)];
    /// let it = input.into_iter().and_then_flat(|i| {
    ///     if i == 0 {
    ///         Err(false)
    ///     } else {
    ///         Ok(((i - 1)..=i))
    ///     }
    /// });
    /// iter_flow::assert_equal(it, vec![Err(false), Err(false), Ok(10), Ok(11)]);
    /// ```
    fn and_then_flat<F, T, U, E, R>(self, op: F) -> flatten::FlattenOk<and_then::AndThen<Self, F>, U, E>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        F: FnMut(T) -> Result<U, R>,
        E: From<R>,
        U: IntoIterator,
    {
        flatten::and_then_flat(self, op)
    }

    /// Return an iterator adaptor that applies the provided fallible closure to every `Result::Ok` value and then
    /// flattens it. `Result::Err` values are unchanged.
    ///
    /// ```
    /// use iter_flow::Iterflow;
    ///
    /// let input = vec![Ok(0), Err(false), Ok(11)];
    /// let it = input.into_iter().and_then_flat_borrow(|i: &i32| {
    ///     if i == &0 {
    ///         Err(false)
    ///     } else {
    ///         Ok(((*i - 1)..=*i))
    ///     }
    /// });
    /// iter_flow::assert_equal(it, vec![Err(false), Err(false), Ok(10), Ok(11)]);
    /// ```
    fn and_then_flat_borrow<F, T, U, E, R>(self, op: F) -> flatten::FlattenOk<and_then::AndThenBorrow<Self, F>, U, E>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        F: FnMut(&T) -> Result<U, R>,
        E: From<R>,
        U: IntoIterator,
    {
        flatten::and_then_flat_borrow(self, op)
    }

    /// `.finish()` is simply a type specialization of [`Iterator::collect`],
    /// for convenience.
    fn finish<T, U, E>(self) -> Result<U, E>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
        Result<U, E>: FromIterator<Result<T, E>>,
    {
        self.collect()
    }

    /// `.finish_vec()` is simply a type specialization of [`Iterator::collect`],
    /// for convenience.
    #[cfg(feature = "use_alloc")]
    fn finish_vec<T, E>(self) -> Result<Vec<T>, E>
    where
        Self: Iterator<Item = Result<T, E>> + Sized,
    {
        self.collect()
    }
}

impl<T: ?Sized> Iterflow for T where T: Iterator {}

/// Assert that two iterables produce equal sequences, with the same
/// semantics as [`equal(a, b)`](equal).
///
/// **Panics** on assertion failure with a message that shows the
/// two iteration elements.
///
/// ```ignore
/// assert_equal("exceed".split('c'), "excess".split('c'));
/// // ^PANIC: panicked at 'Failed assertion Some("eed") == Some("ess") for iteration 1',
/// ```
pub fn assert_equal<I, J>(a: I, b: J)
where
    I: IntoIterator,
    J: IntoIterator,
    I::Item: fmt::Debug + PartialEq<J::Item>,
    J::Item: fmt::Debug,
{
    let mut ia = a.into_iter();
    let mut ib = b.into_iter();
    let mut i = 0;
    loop {
        match (ia.next(), ib.next()) {
            (None, None) => return,
            (a, b) => {
                let equal = match (&a, &b) {
                    (&Some(ref a), &Some(ref b)) => a == b,
                    _ => false,
                };
                assert!(
                    equal,
                    "Failed assertion {a:?} == {b:?} for iteration {i}",
                    i = i,
                    a = a,
                    b = b
                );
                i += 1;
            }
        }
    }
}
