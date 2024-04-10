//! code adapted from https://rust-unofficial.github.io/too-many-lists/first-final.html
#![feature(box_patterns)]

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

#[flux::refined_by(is_some: bool)]
pub enum Opt<T> {
    #[flux::variant(Opt<T>[false])]
    None,
    #[flux::variant((T) -> Opt<T>[true])]
    Some(T),
}

#[flux::trusted]
#[flux::sig(fn(dest: &strg Link<T>[@n], Link<T>[@m]) -> Link<T>[n] ensures dest: Link<T>[m])]
fn replace<T>(dest: &mut Link<T>, src: Link<T>) -> Link<T> {
    std::mem::replace(dest, src)
}

impl<T> Link<T> {
    #[flux::sig(fn(&Link<T>[@n]) -> usize[n])]
    fn len(&self) -> usize {
        match self {
            Link::Empty => 0,
            Link::More(box node) => 1 + node.next.len(),
        }
    }
}

impl<T> List<T> {
    #[flux::sig(fn(self: &strg List<T>[@n], elem: T) ensures self: List<T>[n+1])]
    pub fn push(&mut self, elem: T) {
        let next = replace(&mut self.head, Link::Empty);
        self.head = next;
    } //~ ERROR refinement type

    #[flux::sig(
      fn(self: &strg List<T>[@n]) -> Opt<T>
      ensures self: List<T>[if n > 0 { n - 1 } else { n }]
    )]
    pub fn pop(&mut self) -> Opt<T> {
        match replace(&mut self.head, Link::Empty) {
            Link::Empty => Opt::None,
            Link::More(node) => {
                self.head = node.next;
                Opt::Some(node.elem)
            }
        }
    } //~ ERROR refinement type
}

impl<T> Drop for List<T> {
    #[flux::sig(fn(self: &strg List<T>[@n]) ensures self: List<T>[0])]
    fn drop(&mut self) {
        let mut cur = replace(&mut self.head, Link::Empty);

        while let Link::More(mut boxed_node) = cur {
            cur = replace(&mut boxed_node.next, Link::Empty);
        }
    }
}
