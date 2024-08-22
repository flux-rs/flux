pub const N_BYTES_U64: usize = 8;

pub struct RandomLinearCombination<F, const N: usize> {
    pub cells: [F; N],
}

pub(crate) type U64Word<F> = RandomLinearCombination<F, N_BYTES_U64>;

pub struct ChainIdGadget<F> {
    pub chain_id: U64Word<F>,
}

pub fn test<F>(_g: ChainIdGadget<F>) {}

pub fn bar(_g: U64Word<u64>) {}

impl<F> ChainIdGadget<F> {
    pub fn new(chain_id: U64Word<F>) -> Self {
        Self { chain_id }
    }
}
