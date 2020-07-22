pub mod ast;
pub mod parser;

#[cfg(test)]
mod tests {
    use rustc_ast::attr::with_default_session_globals;
    
    const CPS_SUM_TEXT: &str = "fn sum(n: {i32 | n >= 0}) ret k(v: {i32 | v >= n}) =
  letcont loop(i1: {i32 | i1 >= 0}, r1: {i32 | r1 >= i1}) =
    let t0 = i1 <= n in
    if t0 then
      let t1 = r1 + i1 in
      if t1.1 then
        let t2 = i1 + 1 in
        if t2.1 then jump loop(t1.0, t2.0) else abort
      else
        abort
    else
      jump k(r2)
  in
  let i0 = 0 in
  let r0 = 0 in
  jump loop(i0, r0)
";

    const CPS_COUNT_ZEROS_TEXT: &str = "fn count_zeros(limit: {i32 | n >= 0}) ret k(v: {i32 | v >= 0}) =
  letcont b0(i1: {i32 | i1 >= 0}, c1: {i32 | r1 >= 0}) =
    let t0 = i1 < limit in
    if t0 then
      letcont b1(x: i32) =
        letcont b2(c3: {i32 | c3 >= 0}) =
          let t3 = i1 + 1 in
          if t3.1 then jump b0(i2, t3.0) else abort
        in
        let t1 = x == 0 in
        if t1 then
          let t2 = c1 + 1 in
          if t2.1 then jump b2(t2.0) else abort
        else
          jump b2(c1)
      in
      call f(i1) ret b1
    else
      jump k(c1)
  in
  let i0 = 0 in
  let c0 = 0 in
  jump b0(i0, c0)
";
    #[test]
    fn cps_sum() {
        with_default_session_globals(|| {
            let expr = super::parser::FnsParser::new()
                .parse(CPS_SUM_TEXT)
                .unwrap();

            dbg!(expr);
        });
    }

    #[test]
    fn cps_count_zeros() {
        with_default_session_globals(|| {
            let expr = super::parser::FnsParser::new()
                .parse(CPS_COUNT_ZEROS_TEXT)
                .unwrap();

            dbg!(expr);
        });
    }
}
