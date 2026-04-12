use flux_attrs::*;

fn test01() {}

#[extern_spec]
fn test01(); //~ERROR cannot add extern specs to local definition
