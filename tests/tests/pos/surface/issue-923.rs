#[flux_rs::refined_by(powered:bool)]
pub struct MPU<const MIN_REGION_SIZE: usize> {
    #[field(bool[powered])]
    powered: bool,
}

#[flux_rs::assoc(fn enabled(self: Self) -> bool )]
pub trait MyTrait {
    #[flux_rs::sig(fn(self: &strg Self) ensures self: Self{r: <Self as MyTrait>::enabled(r)})]
    fn enable_app_mpu(&mut self);
}

#[flux_rs::assoc(fn enabled(self: Self) -> bool {self.powered} )]
impl<const MIN_REGION_SIZE: usize> MyTrait for MPU<MIN_REGION_SIZE> {
    #[flux_rs::sig(fn(self: &strg Self) ensures self: Self{r: <Self as MyTrait>::enabled(r)})]
    fn enable_app_mpu(&mut self) {
        self.powered = true;
    }
}
