pub struct CortexMRegion {
    location: Option<(*const u8, usize)>,
}

impl CortexMRegion {
    fn location(&self) -> Option<(*const u8, usize)> {
        self.location
    }
}

fn test(regions: [CortexMRegion; 5]) {
    regions[0].location();
}
