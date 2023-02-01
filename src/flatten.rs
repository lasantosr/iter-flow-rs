use crate::{
    and_then::{self, AndThen, AndThenBorrow},
    map_ok::{self, MapOk, MapOkBorrow},
};

/// An iterator adaptor that flattens `Result::Ok` values and allows `Result::Err` values through unchanged.
#[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
pub struct FlattenOk<I, T, E>
where
    I: Iterator<Item = Result<T, E>>,
    T: IntoIterator,
{
    iter: I,
    inner_front: Option<T::IntoIter>,
}

impl<I, T, E> Iterator for FlattenOk<I, T, E>
where
    I: Iterator<Item = Result<T, E>>,
    T: IntoIterator,
{
    type Item = Result<T::Item, E>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(inner) = &mut self.inner_front {
                if let Some(item) = inner.next() {
                    return Some(Ok(item));
                }
                self.inner_front = None;
            }

            match self.iter.next() {
                Some(Ok(ok)) => self.inner_front = Some(ok.into_iter()),
                Some(Err(e)) => return Some(Err(e)),
                None => return None,
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let inner_front = self
            .inner_front
            .as_ref()
            .map(Iterator::size_hint)
            .unwrap_or((0, Some(0)));
        // The outer iterator `Ok` case could be (0, None) as we don't know its size_hint yet.
        let outer = match self.iter.size_hint() {
            (0, Some(0)) => (0, Some(0)),
            _ => (0, None),
        };

        size_hint_add(inner_front, outer)
    }
}

#[inline]
pub fn size_hint_add(a: (usize, Option<usize>), b: (usize, Option<usize>)) -> (usize, Option<usize>) {
    let min = a.0.saturating_add(b.0);
    let max = match (a.1, b.1) {
        (Some(x), Some(y)) => x.checked_add(y),
        _ => None,
    };

    (min, max)
}

/// Create a new `MapOk` wrapped in a `FlattenOk`.
pub fn flat_map_ok<I, F, T, U, E>(iter: I, f: F) -> FlattenOk<MapOk<I, F>, U, E>
where
    I: Iterator<Item = Result<T, E>>,
    F: FnMut(T) -> U,
    U: IntoIterator,
{
    FlattenOk {
        iter: map_ok::map_ok(iter, f),
        inner_front: None,
    }
}

/// Create a new `MapOkBorrow` wrapped in a `FlattenOk`.
pub fn flat_map_ok_borrow<I, F, T, U, E>(iter: I, f: F) -> FlattenOk<MapOkBorrow<I, F>, U, E>
where
    I: Iterator<Item = Result<T, E>>,
    F: FnMut(&T) -> U,
    U: IntoIterator,
{
    FlattenOk {
        iter: map_ok::map_ok_borrow(iter, f),
        inner_front: None,
    }
}

/// Create a new `AndThen` wrapped in a `FlattenOk`.
pub fn and_then_flat<I, F, T, U, E, R>(iter: I, f: F) -> FlattenOk<AndThen<I, F>, U, E>
where
    I: Iterator<Item = Result<T, E>>,
    F: FnMut(T) -> Result<U, R>,
    E: From<R>,
    U: IntoIterator,
{
    FlattenOk {
        iter: and_then::and_then(iter, f),
        inner_front: None,
    }
}

/// Create a new `AndThen` wrapped in a `FlattenOk`.
pub fn and_then_flat_borrow<I, F, T, U, E, R>(iter: I, f: F) -> FlattenOk<AndThenBorrow<I, F>, U, E>
where
    I: Iterator<Item = Result<T, E>>,
    F: FnMut(&T) -> Result<U, R>,
    E: From<R>,
    U: IntoIterator,
{
    FlattenOk {
        iter: and_then::and_then_borrow(iter, f),
        inner_front: None,
    }
}
