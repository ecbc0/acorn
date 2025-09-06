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