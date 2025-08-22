// Testing conversion of higher-ranked associated type constraint
pub fn map<F: FnOnce(&i32) -> &i32>(f: F) {}
