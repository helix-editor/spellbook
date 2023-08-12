//! Extensions to the stdlib.
//! These are either stabilizing (like `is_some_and`) or custom.

pub(crate) fn is_none_or<T, F>(opt: Option<T>, f: F) -> bool
where
    F: FnOnce(T) -> bool,
{
    match opt {
        Some(val) => f(val),
        None => true,
    }
}

pub(crate) fn is_some_and<T, F>(opt: Option<T>, f: F) -> bool
where
    F: FnOnce(T) -> bool,
{
    match opt {
        Some(val) => f(val),
        None => false,
    }
}

/// An iterator that wraps two possible iterators which produce the same type.
/// Useful for combining iterators like [std::iter::once] and [std::iter::empty].
pub(crate) enum EitherIterator<T, L: Iterator<Item = T>, R: Iterator<Item = T>> {
    Left(L),
    Right(R),
}

impl<T, L, R> Iterator for EitherIterator<T, L, R>
where
    L: Iterator<Item = T>,
    R: Iterator<Item = T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            Self::Left(iter) => iter.next(),
            Self::Right(iter) => iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            Self::Left(iter) => iter.size_hint(),
            Self::Right(iter) => iter.size_hint(),
        }
    }
}

/// Checks if an iterator constantly produces only one value.
/// If the iterator is empty this function returns `false`.
pub(crate) fn iter_is_one_value<T: Eq, I: Iterator<Item = T>>(iter: I) -> bool {
    let mut value = None;
    for element in iter {
        match value.as_ref() {
            Some(val) if val == &element => (),
            Some(_other) => return false,
            None => value = Some(element),
        }
    }
    value.is_some()
}
