#![flux::sort(opaque GhostTokenId)]

use std::{cell::UnsafeCell, mem};

#[flux::opaque]
#[flux::refined_by(id: GhostTokenId)]
pub struct GhostToken(Private);

impl GhostToken {
    #[flux::trusted]
    #[flux::sig(fn() -> GhostToken)]
    pub fn new() -> GhostToken {
        GhostToken(Private)
    }
}

struct Private;

#[repr(transparent)]
#[flux::opaque]
#[flux::refined_by(id: GhostTokenId)]
pub struct GhostCell<T: ?Sized> {
    value: UnsafeCell<T>,
}

impl<T> GhostCell<T> {
    #[flux::trusted]
    #[flux::sig(fn(value: T, token: &GhostToken[@id]) -> GhostCell<T>[id])]
    pub const fn new(value: T, _: &GhostToken) -> Self {
        Self { value: UnsafeCell::new(value) }
    }

    #[flux::trusted]
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }
}

impl<T: ?Sized> GhostCell<T> {
    #[flux::trusted]
    #[flux::sig(fn(&GhostCell<T>[id], &GhostToken[@id]) -> &T)]
    pub fn borrow<'a>(&'a self, _: &'a GhostToken) -> &'a T {
        unsafe { &*self.value.get() }
    }

    #[flux::trusted]
    #[flux::sig(fn(&GhostCell<T>[id], &mut GhostToken[@id]) -> &mut T)]
    pub fn borrow_mut<'a>(&'a self, _: &'a mut GhostToken) -> &'a mut T {
        unsafe { &mut *self.value.get() }
    }

    #[flux::trusted]
    pub fn get_mut(&mut self) -> &mut T {
        unsafe { mem::transmute(self) }
    }
}

#[forbid(unsafe_code)]
impl<T> GhostCell<T> {
    #[flux::sig(fn(&GhostCell<T>[id], T, &mut GhostToken[@id]) -> T)]
    pub fn replace(&self, value: T, token: &mut GhostToken) -> T {
        mem::replace(self.borrow_mut(token), value)
    }

    #[flux::sig(fn(&GhostCell<T>[id], &mut GhostToken[@id]) -> T)]
    pub fn take(&self, token: &mut GhostToken) -> T
    where
        T: Default,
    {
        self.replace(T::default(), token)
    }
}

unsafe impl<T: ?Sized + Send> Send for GhostCell<T> {}

unsafe impl<T: ?Sized + Send + Sync> Sync for GhostCell<T> {}
