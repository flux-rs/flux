use std::{collections::HashMap, rc::Rc};

use super::ast::{Field, Var};

type Place = (Var, Vec<u32>);

#[derive(Debug, Clone)]
pub struct Subst(Rc<HashMap<Var, Place>>);

impl Subst {
    pub fn new(m: HashMap<Var, Place>) -> Self {
        Self(Rc::new(m))
    }

    pub fn empty() -> Self {
        Self(Rc::new(HashMap::new()))
    }

    pub fn get(&self, x: Var) -> Option<Place> {
        self.0.get(&x).cloned()
    }

    pub fn extend<I, K, V>(&self, iter: I) -> Self
    where
        I: IntoIterator<Item = (K, V)>,
        K: Into<Var>,
        V: Into<Place>,
    {
        let mut m: HashMap<Var, Place> = iter
            .into_iter()
            .map(|(x, y)| (x.into(), y.into()))
            .collect();
        for (x, (y, p1)) in self.0.iter() {
            if let Some((z, mut p2)) = m.get(y).cloned() {
                p2.extend(p1);
                m.insert(*x, (z, p2));
            } else {
                m.insert(*x, (*y, p1.clone()));
            }
        }
        Self(Rc::new(m))
    }

    pub fn extend2<I1, I2, K, V>(&self, iter1: I1, iter2: I2) -> Self
    where
        I1: IntoIterator<Item = K>,
        I2: IntoIterator<Item = V>,
        K: Into<Var>,
        V: Into<Place>,
    {
        self.extend(iter1.into_iter().zip(iter2))
    }
}

impl From<Var> for Place {
    fn from(x: Var) -> Self {
        (x.into(), vec![])
    }
}

impl From<Field> for Place {
    fn from(x: Field) -> Self {
        (x.into(), vec![])
    }
}

impl<I, A, B> From<I> for Subst
where
    I: IntoIterator<Item = (A, B)>,
    A: Into<Var>,
    B: Into<Place>,
{
    fn from(it: I) -> Self {
        Self(Rc::new(
            it.into_iter().map(|(x, y)| (x.into(), y.into())).collect(),
        ))
    }
}

#[derive(Debug, Clone)]
pub struct DeferredSubst<T>(Subst, T);

impl<T> DeferredSubst<&T> {
    pub fn get<K, V>(&self, k: K) -> DeferredSubst<V>
    where
        T: std::ops::Index<K, Output = V>,
        V: Copy,
    {
        DeferredSubst(self.0.clone(), self.1[k])
    }
}

impl<T> DeferredSubst<T> {
    pub fn new(subst: Subst, x: T) -> Self {
        DeferredSubst(subst, x)
    }

    pub fn empty(x: T) -> Self {
        DeferredSubst(Subst::empty(), x)
    }

    pub fn split(self) -> (Subst, T) {
        (self.0, self.1)
    }
}

impl<T> DeferredSubst<T> {
    pub fn apply<S>(self) -> S
    where
        T: ApplySubst<S>,
    {
        let (subst, x) = self.split();
        x.apply(&subst)
    }
}

impl<T> From<T> for DeferredSubst<T> {
    fn from(x: T) -> Self {
        DeferredSubst::empty(x)
    }
}

pub trait ApplySubst<T> {
    fn apply(&self, subst: &Subst) -> T;
}
