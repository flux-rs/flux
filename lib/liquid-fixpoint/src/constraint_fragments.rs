use crate::{
    Types,
    constraint::{Bind, Constraint, Pred},
};

pub enum Fragment<'a, T: Types> {
    Constraint(&'a Constraint<T>),
    Predicate(&'a Pred<T>),
}

pub struct ConstraintFragments<'a, T: Types> {
    stack: Vec<(Fragment<'a, T>, Vec<Bind<T>>)>,
}

impl<'a, T: Types> ConstraintFragments<'a, T> {
    pub fn new(cstr: &'a Constraint<T>) -> Self {
        ConstraintFragments { stack: vec![(Fragment::Constraint(cstr), vec![])] }
    }
}

impl<T: Types> Iterator for ConstraintFragments<'_, T> {
    type Item = Constraint<T>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, binders)) = self.stack.pop() {
            match node {
                Fragment::Predicate(Pred::And(preds)) => {
                    for p in preds.iter().rev() {
                        self.stack.push((Fragment::Predicate(p), binders.clone()));
                    }
                }
                Fragment::Predicate(pred) => {
                    let mut result = Constraint::Pred(pred.clone(), None);
                    for b in binders.iter().rev() {
                        result = Constraint::ForAll(b.clone(), Box::new(result));
                    }
                    return Some(result);
                }
                Fragment::Constraint(Constraint::Pred(pred, _tag)) => {
                    self.stack
                        .push((Fragment::Predicate(pred), binders.clone()));
                }
                Fragment::Constraint(Constraint::Conj(children)) => {
                    for child in children.iter().rev() {
                        self.stack
                            .push((Fragment::Constraint(child), binders.clone()));
                    }
                }
                Fragment::Constraint(Constraint::ForAll(bind, inner)) => {
                    let mut new_binders = binders.clone();
                    new_binders.push(bind.clone());
                    self.stack
                        .push((Fragment::Constraint(&**inner), new_binders));
                }
            }
        }
        None
    }
}
