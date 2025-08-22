use std::{collections::HashMap, fs, io};

use flux_config as config;
use rustc_ast::{DelimArgs, tokenstream::TokenTree};
use rustc_hir::{AttrArgs, def_id::LOCAL_CRATE};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, source_map::SourceMap};
use serde::Serialize;

#[derive(Default, Serialize)]
pub struct Stats {
    /// The number of times an attribute appears, e.g., how many times `flux::trusted` appears.
    attr_count: HashMap<String, usize>,
    /// The number of lines taken by each type of attribute, e.g., the sum of all lines taken by
    /// `flux::sig` annotations.
    loc_per_attr: HashMap<String, usize>,
    /// This is the sum over `loc_per_attr`
    loc: usize,
}

impl Stats {
    pub fn save(&self, tcx: TyCtxt) -> io::Result<()> {
        fs::create_dir_all(config::log_dir())?;
        let crate_name = tcx.crate_name(LOCAL_CRATE);
        let path = config::log_dir().join(format!("{crate_name}-annots.json"));
        let mut file = fs::File::create(path)?;
        serde_json::to_writer(&mut file, self)?;
        Ok(())
    }

    pub fn add(&mut self, tcx: TyCtxt, name: &str, args: &AttrArgs) {
        let sm = tcx.sess.source_map();
        self.increase_count(name);
        match args {
            AttrArgs::Empty => {
                self.increase_loc(name, 1);
            }
            AttrArgs::Delimited(delim_args) => {
                self.increase_loc(name, count_lines(sm, delim_args));
            }
            AttrArgs::Eq { .. } => {}
        }
    }

    fn increase_count(&mut self, name: &str) {
        if let Some(count) = self.attr_count.get_mut(name) {
            *count += 1;
        } else {
            self.attr_count.insert(name.to_string(), 1);
        }
    }

    fn increase_loc(&mut self, name: &str, loc: usize) {
        if let Some(count) = self.loc_per_attr.get_mut(name) {
            *count += loc;
        } else {
            self.loc_per_attr.insert(name.to_string(), loc);
        }
        self.loc += loc;
    }
}

fn count_lines(sm: &SourceMap, delim_args: &DelimArgs) -> usize {
    fn go<'a>(
        sm: &SourceMap,
        line_set: &mut IntervalSet,
        tokens: impl Iterator<Item = &'a TokenTree>,
    ) {
        for t in tokens {
            match t {
                TokenTree::Token(token, _) => {
                    let info = get_lines(sm, token.span);
                    line_set.insert(info.start_line, info.end_line);
                }
                TokenTree::Delimited(delim_span, _, _, token_stream) => {
                    let open_info = get_lines(sm, delim_span.open);
                    let close_info = get_lines(sm, delim_span.close);
                    line_set.insert(open_info.start_line, open_info.end_line);
                    line_set.insert(close_info.start_line, close_info.end_line);
                    go(sm, line_set, token_stream.iter());
                }
            }
        }
    }
    let mut line_set = IntervalSet::new();
    go(sm, &mut line_set, delim_args.tokens.iter());
    let mut lines = 0;
    for (start, end) in line_set.iter_intervals() {
        lines += end - start + 1;
    }
    lines
}

#[expect(dead_code)]
struct LineInfo {
    start_line: usize,
    start_col: usize,
    end_line: usize,
    end_col: usize,
}

fn get_lines(sm: &SourceMap, span: Span) -> LineInfo {
    let lines = sm.span_to_location_info(span);
    LineInfo { start_line: lines.1, start_col: lines.2, end_line: lines.3, end_col: lines.4 }
}

struct IntervalSet {
    map: Vec<(usize, usize)>,
}

impl IntervalSet {
    fn new() -> Self {
        Self { map: vec![] }
    }

    fn insert(&mut self, start: usize, end: usize) {
        if start > end {
            return;
        }

        // This condition looks a bit weird, but actually makes sense.
        //
        // if r.0 == end + 1, then we're actually adjacent, so we want to
        // continue to the next range. We're looking here for the first
        // range which starts *non-adjacently* to our end.
        let next = self.map.partition_point(|r| r.0 <= end + 1);

        if let Some(right) = next.checked_sub(1) {
            let (prev_start, prev_end) = self.map[right];
            if prev_end + 1 >= start {
                // If the start for the inserted range is adjacent to the
                // end of the previous, we can extend the previous range.
                if start < prev_start {
                    // The first range which ends *non-adjacently* to our start.
                    // And we can ensure that left <= right.

                    let left = self.map.partition_point(|l| l.1 + 1 < start);
                    let min = std::cmp::min(self.map[left].0, start);
                    let max = std::cmp::max(prev_end, end);
                    self.map[right] = (min, max);
                    if left != right {
                        self.map.drain(left..right);
                    }
                } else {
                    // We overlap with the previous range, increase it to
                    // include us.
                    //
                    // Make sure we're actually going to *increase* it though --
                    // it may be that end is just inside the previously existing
                    // set.
                    if end > prev_end {
                        self.map[right].1 = end;
                    }
                }
            } else {
                // Otherwise, we don't overlap, so just insert
                self.map.insert(right + 1, (start, end));
            }
        } else if self.map.is_empty() {
            // Quite common in practice, and expensive to call memcpy
            // with length zero.
            self.map.push((start, end));
        } else {
            self.map.insert(next, (start, end));
        }
    }

    fn iter_intervals(&self) -> impl Iterator<Item = (usize, usize)> {
        self.map.iter().copied()
    }
}
