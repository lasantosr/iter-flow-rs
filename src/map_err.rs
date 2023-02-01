#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct MapErrBy<I, F> {
    iter: I,
    f: F,
}

pub trait MapErrPredicate<E> {
    type Out;
    fn call(&mut self, e: E) -> Self::Out;
}

impl<I, F, T, E> Iterator for MapErrBy<I, F>
where
    I: Iterator<Item = Result<T, E>>,
    F: MapErrPredicate<E>,
{
    type Item = Result<T, F::Out>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|e| e.map_err(|e| self.f.call(e)))
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
        self.iter
            .fold(init, move |acc, v| fold_f(acc, v.map_err(|e| f.call(e))))
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        let mut f = self.f;
        self.iter.map(move |v| v.map_err(|e| f.call(e))).collect()
    }
}

/// An iterator adaptor that maps the inner error
///
/// See [`.map_err()`](crate::Iterflow::map_err) for more information.
pub type MapErr<I, F> = MapErrBy<I, MapErrFn<F>>;

impl<F, E, O> MapErrPredicate<E> for MapErrFn<F>
where
    F: FnMut(E) -> O,
{
    type Out = O;

    fn call(&mut self, e: E) -> Self::Out {
        self.0(e)
    }
}

#[derive(Clone)]
pub struct MapErrFn<F>(F);

/// Create a new `MapErr`.
pub fn map_err<I, F, E, O>(iter: I, f: F) -> MapErr<I, F>
where
    I: Iterator,
    F: FnMut(E) -> O,
{
    MapErr { iter, f: MapErrFn(f) }
}
