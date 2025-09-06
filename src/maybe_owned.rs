use std::ops::Deref;

pub enum MaybeOwned<'a, T: ?Sized> {
    Borrowed(&'a T),
    Owned(Box<T>),
}

impl<'a, T: ?Sized> AsRef<T> for MaybeOwned<'a, T> {
    fn as_ref(&self) -> &T {
        match self {
            MaybeOwned::Borrowed(t) => t,
            MaybeOwned::Owned(b) => b,
        }
    }
}

impl<'a, T: ?Sized> Deref for MaybeOwned<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            MaybeOwned::Borrowed(t) => t,
            MaybeOwned::Owned(b) => b,
        }
    }
}