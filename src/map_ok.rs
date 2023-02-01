#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct MapOkBy<I, F> {
    iter: I,
    f: F,
}

pub trait MapOkPredicate<T> {
    type Out;
    fn call(&mut self, t: T) -> Self::Out;
}

impl<I, F, T, E> Iterator for MapOkBy<I, F>
where
    I: Iterator<Item = Result<T, E>>,
    F: MapOkPredicate<T>,
{
    type Item = Result<F::Out, E>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|e| e.map(|t| self.f.call(t)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn fold<Acc, Fold>(self, init: Acc, mut fold_f: Fold) -> Acc
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let mut f = self.f;
        self.iter.fold(init, move |acc, v| fold_f(acc, v.map(|t| f.call(t))))
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        let mut f = self.f;
        self.iter.map(move |v| v.map(|t| f.call(t))).collect()
    }
}

/// An iterator adaptor that maps the inner value
///
/// See [`.map_ok()`](crate::Iterflow::map_ok) for more information.
pub type MapOk<I, F> = MapOkBy<I, MapOkFn<F>>;

impl<F, T, O> MapOkPredicate<T> for MapOkFn<F>
where
    F: FnMut(T) -> O,
{
    type Out = O;

    fn call(&mut self, t: T) -> Self::Out {
        self.0(t)
    }
}

#[derive(Clone)]
pub struct MapOkFn<F>(F);

/// Create a new `MapOk`.
pub fn map_ok<I, F, E, O>(iter: I, f: F) -> MapOk<I, F>
where
    I: Iterator,
    F: FnMut(E) -> O,
{
    MapOk { iter, f: MapOkFn(f) }
}

#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct MapOkBorrowBy<I, F> {
    iter: I,
    f: F,
}

pub trait MapOkBorrowPredicate<T> {
    type Out;
    fn call(&mut self, t: &T) -> Self::Out;
}

impl<I, F, T, E> Iterator for MapOkBorrowBy<I, F>
where
    I: Iterator<Item = Result<T, E>>,
    F: MapOkBorrowPredicate<T>,
{
    type Item = Result<F::Out, E>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|e| e.map(|t| self.f.call(&t)))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn fold<Acc, Fold>(self, init: Acc, mut fold_f: Fold) -> Acc
    where
        Self: Sized,
        Fold: FnMut(Acc, Self::Item) -> Acc,
    {
        let mut f = self.f;
        self.iter.fold(init, move |acc, v| fold_f(acc, v.map(|t| f.call(&t))))
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        let mut f = self.f;
        self.iter.map(move |v| v.map(|t| f.call(&t))).collect()
    }
}

/// An iterator adaptor that maps the inner value
///
/// See [`.map_ok_borrow()`](crate::Iterflow::map_ok_borrow) for more information.
pub type MapOkBorrow<I, F> = MapOkBorrowBy<I, MapOkBorrowFn<F>>;

impl<F, T, O> MapOkBorrowPredicate<T> for MapOkBorrowFn<F>
where
    F: FnMut(&T) -> O,
{
    type Out = O;

    fn call(&mut self, t: &T) -> Self::Out {
        self.0(t)
    }
}

#[derive(Clone)]
pub struct MapOkBorrowFn<F>(F);

/// Create a new `MapOkBorrow`.
pub fn map_ok_borrow<I, F, E, O>(iter: I, f: F) -> MapOkBorrow<I, F>
where
    I: Iterator,
    F: FnMut(&E) -> O,
{
    MapOkBorrow {
        iter,
        f: MapOkBorrowFn(f),
    }
}
