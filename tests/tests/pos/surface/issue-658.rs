pub struct ListLink<'a>(&'a usize);

pub trait ListNode<'a> {
    fn next(&'a self) -> &'a ListLink<'a>;
}

fn next_link<'a, T: ListNode<'a>>(res: &'a T) -> &'a ListLink<'a> {
    res.next()
}
