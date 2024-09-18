use flux_rs::*;

#[refined_by(val: int)]
enum Color {
    #[variant(Color[1])]
    Red,
    #[variant(Color[2])]
    Green,
    #[variant(Color[3])]
    Blue,
}

#[sig(fn(_, &Color[@c]) -> Result<usize{v: v >= c}, ()>)]
fn add_colorcode(num: Result<usize, ()>, color: &Color) -> Result<usize, ()> {
    num.map(|n| {
        match color {
            Color::Red => n + 1,
            Color::Green => n + 2,
            Color::Blue => n + 3,
        }
    })
}
