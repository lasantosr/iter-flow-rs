#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct AndThenBy<I, F> {
    iter: I,
    f: F,
}

pub trait AndThenPredicate<T> {
    type Out;
    type Err;
    fn call(&mut self, t: T) -> Result<Self::Out, Self::Err>;
}

impl<I, F, T, E> Iterator for AndThenBy<I, F>
where
    I: Iterator<Item = Result<T, E>>,
    F: AndThenPredicate<T>,
    E: From<<F as AndThenPredicate<T>>::Err>,
{
    type Item = Result<F::Out, E>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|r| match r {
            Ok(t) => match self.f.call(t) {
                Ok(o) => Ok(o),
                Err(err) => Err(err.into()),
            },
            Err(err) => Err(err),
        })
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
        self.iter.fold(init, move |acc, r| {
            fold_f(
                acc,
                match r {
                    Ok(t) => match f.call(t) {
                        Ok(o) => Ok(o),
                        Err(err) => Err(err.into()),
                    },
                    Err(err) => Err(err),
                },
            )
        })
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        let mut f = self.f;
        self.iter
            .map(move |r| match r {
                Ok(t) => match f.call(t) {
                    Ok(o) => Ok(o),
                    Err(err) => Err(err.into()),
                },
                Err(err) => Err(err),
            })
            .collect()
    }
}

/// An iterator adaptor that maps the inner value
///
/// See [`.and_then()`](crate::Iterflow::and_then) for more information.
pub type AndThen<I, F> = AndThenBy<I, AndThenFn<F>>;

impl<F, T, O, E> AndThenPredicate<T> for AndThenFn<F>
where
    F: FnMut(T) -> Result<O, E>,
{
    type Err = E;
    type Out = O;

    fn call(&mut self, t: T) -> Result<Self::Out, Self::Err> {
        self.0(t)
    }
}

#[derive(Clone)]
pub struct AndThenFn<F>(F);

/// Create a new `AndThen`.
pub fn and_then<I, F, T, O, E>(iter: I, f: F) -> AndThen<I, F>
where
    I: Iterator,
    F: FnMut(T) -> Result<O, E>,
{
    AndThen { iter, f: AndThenFn(f) }
}

#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct AndThenBorrowBy<I, F> {
    iter: I,
    f: F,
}

pub trait AndThenBorrowPredicate<T> {
    type Out;
    type Err;
    fn call(&mut self, t: &T) -> Result<Self::Out, Self::Err>;
}

impl<I, F, T, E> Iterator for AndThenBorrowBy<I, F>
where
    I: Iterator<Item = Result<T, E>>,
    F: AndThenBorrowPredicate<T>,
    E: From<<F as AndThenBorrowPredicate<T>>::Err>,
{
    type Item = Result<F::Out, E>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|r| match r {
            Ok(t) => match self.f.call(&t) {
                Ok(o) => Ok(o),
                Err(err) => Err(err.into()),
            },
            Err(err) => Err(err),
        })
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
        self.iter.fold(init, move |acc, r| {
            fold_f(
                acc,
                match r {
                    Ok(t) => match f.call(&t) {
                        Ok(o) => Ok(o),
                        Err(err) => Err(err.into()),
                    },
                    Err(err) => Err(err),
                },
            )
        })
    }

    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        let mut f = self.f;
        self.iter
            .map(move |r| match r {
                Ok(t) => match f.call(&t) {
                    Ok(o) => Ok(o),
                    Err(err) => Err(err.into()),
                },
                Err(err) => Err(err),
            })
            .collect()
    }
}

/// An iterator adaptor that maps the inner value
///
/// See [`.and_then_borrow()`](crate::Iterflow::and_then_borrow) for more information.
pub type AndThenBorrow<I, F> = AndThenBorrowBy<I, AndThenBorrowFn<F>>;

impl<F, T, O, E> AndThenBorrowPredicate<T> for AndThenBorrowFn<F>
where
    F: FnMut(&T) -> Result<O, E>,
{
    type Err = E;
    type Out = O;

    fn call(&mut self, t: &T) -> Result<Self::Out, Self::Err> {
        self.0(t)
    }
}

#[derive(Clone)]
pub struct AndThenBorrowFn<F>(F);

/// Create a new `AndThen`.
pub fn and_then_borrow<I, F, E, O>(iter: I, f: F) -> AndThenBorrow<I, F>
where
    I: Iterator,
    F: FnMut(&E) -> O,
{
    AndThenBorrow {
        iter,
        f: AndThenBorrowFn(f),
    }
}
