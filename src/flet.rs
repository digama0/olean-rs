
pub struct Flet<'a, T>(&'a mut T, Option<T>);

impl<'a, T> Flet<'a, T> {
    pub fn new(val: &'a mut T, new: T) -> Flet<'a, T> {
        let old = std::mem::replace(val, new);
        Flet(val, Some(old))
    }
}
impl<'a, T> Drop for Flet<'a, T> {
    fn drop(&mut self) {
        if let Some(t) = self.1.take() { *self.0 = t }
    }
}
