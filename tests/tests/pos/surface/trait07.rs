pub struct LInt<const L: usize>([u64; L]);

impl<const L: usize> std::ops::Add<LInt<L>> for LInt<L> {
    type Output = LInt<L>;
    fn add(self, other: Self) -> Self::Output {
        todo!()
    }
}

fn test00(a: LInt<4>, b: LInt<4>) -> LInt<4> {
    a + b
}
