use flux_rs::*;

#[assoc(fn can_fit(self: Self, animal: Self::Animal) -> bool)]
trait Barn {
    type Animal;

    #[sig(fn(self: &mut Self[@barn], animal: Self::Animal{ <Self as Barn>::can_fit(barn, animal) }))]
    fn put_animal_in_house(&mut self, animal: Self::Animal);
}

#[refined_by(size: int)]
struct Horse {
    #[field(i32[size])]
    size: i32,
}

#[refined_by(max_size: int)]
struct HorseBarn {
    #[field(i32[max_size])]
    max_size: i32,
}

#[assoc(fn can_fit(self: HorseBarn, horse: Horse) -> bool { horse.size <= self.max_size })]
impl Barn for HorseBarn {
    type Animal = Horse;

    #[trusted]
    #[sig(fn(self: &mut Self[@barn], horse: Horse { horse.size < barn.max_size}))]
    fn put_animal_in_house(&mut self, horse: Horse) {}
}

fn test00() {
    let mut barn = HorseBarn { max_size: 20 };
    let horse = Horse { size: 10 };

    barn.put_animal_in_house(horse);
}
