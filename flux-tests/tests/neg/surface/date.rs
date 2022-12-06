#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::dfn(is_btwn(v:int, lo:int, hi: int) -> bool { lo <= v && v <= hi })]
#![flux::dfn(ok_day(d:int) -> bool { is_btwn(d, 1, 31) })]
#![flux::dfn(is_month30(m:int) -> bool { m == 4 || m == 6 || m == 9 || m == 11 })]
#![flux::dfn(ok_month(d:int, m:int) -> bool { is_btwn(m, 1, 12) && (is_month30(m) => d <= 30) })]
#![flux::dfn(is_leap_year(y:int) -> bool { y % 400 == 0 || (y % 4 == 0 && (y % 100) > 0) })]
#![flux::dfn(is_feb_day(d:int, y:int) -> bool { d <= 29 && ( d == 29 => is_leap_year(y) ) })]
#![flux::dfn(ok_year(d:int, m:int, y:int) -> bool { 1 <= y && (m == 2 => is_feb_day(d, y)) })]

// https://github.com/chrisdone/sandbox/blob/master/liquid-haskell-dates.hs

#[allow(dead_code)]
#[flux::refined_by(d:int, m:int, y:int)]
pub struct Date {
    #[flux::field({ usize[@d] : ok_day(d) })]
    day: usize,
    #[flux::field({ usize[@m] : ok_month(d, m)})]
    month: usize,
    #[flux::field({ usize[@y] : ok_year(d, m, y)})]
    year: usize,
}

pub fn test() {
    let _bad_date = Date { //~ ERROR precondition
      day: 31,
      month: 6, // June has 30 days
      year: 1977,
    };
}

