pub mod ast;
pub mod constraint;
pub mod context;
pub mod liquid;
pub mod parser;
pub mod subst;
pub mod typeck;
pub mod utils;

#[cfg(test)]
mod tests {
    use super::{
        ast::FnDef,
        constraint::{Constraint, Kvar},
        liquid::LiquidSolver,
        parser::FnParser,
    };
    use super::{
        context::{Arena, LiquidRustCtxt},
        typeck::TypeCk,
    };
    use rustc_ast::attr::with_default_session_globals;

    struct Session<'lr> {
        cx: &'lr LiquidRustCtxt<'lr>,
    }

    impl<'lr> Session<'lr> {
        fn run(act: impl for<'a> FnOnce(Session<'a>)) {
            with_default_session_globals(|| {
                let arena = Arena::default();
                let cx = LiquidRustCtxt::new(&arena);
                act(Session { cx: &cx });
            })
        }

        fn parse(&self, string: &str) -> Option<FnDef<'lr>> {
            FnParser::new().parse(self.cx, &mut 0, string).ok()
        }

        fn check(&self, string: &str) -> (Constraint, Vec<Kvar>) {
            TypeCk::cgen(self.cx, &self.parse(string).unwrap()).unwrap()
        }
    }

    #[test]
    fn abs() {
        Session::run(|sess| {
            let (c, kvars) = sess.check(
                r####"
fn abs(n0: {int | true}; n: own(n0)) ret k(r: {int | V >= 0}; own(r)) =
  let b = new(1);
  b := *n <= 0;
  if *b then
    n := 0 - *n;
    jump k(n)
  else
    jump k(n)
"####,
            );
            assert!(LiquidSolver::new().unwrap().check(&c, &kvars).unwrap());
        });
    }

    #[test]
    fn sum() {
        Session::run(|sess| {
            let (c, kvars) = sess.check(
                r####"
    fn sum(n0: {int | V >= 0}; n: own(n0)) ret k(r: {int | V >= n0}; own(r)) =
      letcont loop( n1: {int | _ }, i1: {int | _ }, r1: {int | _ }
                  ; i: own(i1), r: own(r1), n: own(n1);) =
        let t0 = new(1);
        t0 := *i <= *n;
        if *t0 then
          i := *i + 1;
          r := *r + *i;
          jump loop()
        else
          jump k(r)
      in
      let i = new(1);
      let r = new(1);
      i := 0;
      r := 0;
      jump loop()
    "####,
            );
            assert!(LiquidSolver::new().unwrap().check(&c, &kvars).unwrap());
        })
    }

    #[test]
    fn count_zeros() {
        Session::run(|sess| {
            let p = sess.parse(
                r####"
    fn count_zeros(n0: {int | V >= 0}; n: own(n0)) ret k(r: {int | V >= 0}; own(r))=
      letcont b0( n1: {int | V >= 0}, i1: {int | V >= 0}, c1: {int | V >= 0}
                ; i: own(i1), c: own(c1), n: own(n1); ) =
        let t0 = new(1);
        t0 := *i < *n;
        if *t0 then
          letcont b1( n2: {int | V >= 0}, i2: {int | V >= 0}, c2: {int | V >= 0}, x0: {int | true}
                    ; i: own(i2), c: own(c2), n: own(n2)
                    ; x: own(x0)
                    ) =
            let t1 = new(1);
            t1 := *x == 0;
            if *t1 then
              c := *c + 1;
              jump b0()
            else
              jump b0()
          in
          call f(i) ret b1
        else
          jump k(c)
      in
      let i = new(1);
      let c = new(1);
      i := 0;
      c := 0;
      jump b0()
    "####,
            );
            assert!(p.is_some());
        });
    }

    #[test]
    fn alloc_pair() {
        Session::run(|sess| {
            let (c, kvars) = sess.check(
                r####"
    fn alloc_pair(;) ret k(r: {int | true}; own(r))=
      let p = new((1, 1));
      p.0 := 1;
      p.1 := 2;
      let r = new(1);
      r := *p.0;
      jump k(r)
    "####,
            );
            assert!(LiquidSolver::new().unwrap().check(&c, &kvars).unwrap());
        });
    }

    #[test]
    fn length() {
        Session::run(|sess| {
            let (c, kvars) = sess.check(
                r####"
    fn length(p0: (@x: {int | true}, @y: {int | V >= @x}); p: own(p0)) ret k(r: {int | V >= 0}; own(r))=
      let t = new(1);
      t := *p.1 - *p.0;
      jump k(t)
    "####,
            );
            assert!(LiquidSolver::new().unwrap().check(&c, &kvars).unwrap());
        });
    }

    #[test]
    fn pair_subtyping() {
        Session::run(|sess| {
            let (c, kvars) = sess.check(
                r####"
    fn foo(;) ret k(r0: (@x: {int | true}, @y: {int | V >= @x}); own(r0))=
      let p = new((1, 1));
      p.0 := 0;
      p.1 := 1;
      jump k(p)
    "####,
            );
            assert!(LiquidSolver::new().unwrap().check(&c, &kvars).unwrap());
        });
    }

    #[test]
    fn kvar_with_tuples() {
        Session::run(|sess| {
            let (c, kvars) = sess.check(
                r####"
    fn foo(x0: (@a: {int | true}, @b: {int | V > @a}); x: own(x0)) ret k(r0: {int | V >= x0.0}; own(r0))=
      letcont b0(y1: {int | _ }; ; y: own(y1)) =
        jump k(y)
      in
      let y = new(1);
      y := *x.1;
      jump k(y)
    "####,
            );
            assert!(LiquidSolver::new().unwrap().check(&c, &kvars).unwrap());
        });
    }
}
