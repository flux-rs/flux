#[flux_rs::trusted]
pub fn get_filter_map(
) -> core::iter::FilterMap<core::slice::Iter<'static, Option<()>>, fn(&Option<()>) -> Option<()>> {
    unimplemented!()
}

fn use_filter_map() {
    let found = get_filter_map().find(|_| true);
}
