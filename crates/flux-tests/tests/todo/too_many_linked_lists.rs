//! code adapted from https://rust-unofficial.github.io/too-many-lists/first-final.html
#![feature(register_tool, box_patterns)]

#[flux::refined_by(len: int)]
pub struct List<T> {
    #[flux::field(Link<T>[len])]
    head: Link<T>,
}

#[flux::refined_by(len: int)]
enum Link<T> {
    #[flux::variant(Link<T>[0])]
    Empty,
    #[flux::variant((Box<Node<T>[@n]>) -> Link<T>[n + 1])]
    More(Box<Node<T>>),
}

#[flux::refined_by(len: int)]
struct Node<T> {
    elem: T,
    #[flux::field(Link<T>[len])]
    next: Link<T>,
}

#[flux::trusted]
#[flux::sig(fn(dest: &strg Link<T>[@n], Link<T>[@m]) -> Link<T>[n] ensures dest: Link<T>[m])]
fn replace<T>(dest: &mut Link<T>, src: Link<T>) -> Link<T> {
    std::mem::replace(dest, src)
}

impl<T> Drop for List<T> {
    // #[flux::sig(fn(&mut List<T>[@n]))] fails with parameter inference error (we shouldn't be able to verify the function with this, but at least it it should not fail)
    // #[flux::sig(fn(&mut List<T>))] panics because it cannot unfold the existential under &mut
    fn drop(&mut self) {
        let mut cur = replace(&mut self.head, Link::Empty);

        while let Link::More(mut boxed_node) = cur {
            cur = replace(&mut boxed_node.next, Link::Empty);
        }
    }
}
