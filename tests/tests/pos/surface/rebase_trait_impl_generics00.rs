use std::ops::RangeInclusive;

pub fn test(r: RangeInclusive<usize>) {
    r.fold(0, |res, _| res);
}
