#![allow(unused_attributes)]
#![feature(register_tool)]
#![register_tool(lr)]

#[path = "../../lib/rmat.rs"]
pub mod rmat;
use rmat::RMat;

/* step 1 */

#[lr::sig(fn (arr2: &RMat<f32>[m,n], m:usize{0 < m}, n: usize{ 0 < n}) -> bool)]
pub fn is_neg(arr2: &RMat<f32>, _m:usize, n: usize) -> bool {
  let mut j = 1;
  while j < n - 1 {
    if *arr2.get(0, j) < 0.0 {
      return true
    }
    j += 1;
  }
  false
}

/* step 2 */

#[lr::sig(fn (m:usize{0 < m}, n:usize{0 < n}, arr2: &RMat<f32>[m, n]) -> bool)]
pub fn unb1(m:usize, n:usize, arr2: &RMat<f32>) -> bool {
  let mut i = 0;
  let mut j = 1;

  // INV: 0 < i <= m, 0 <= j < n
  while j < n - 1 {
    if *arr2.get(0, j) < 0.0 {
      i = i + 1;
      loop {
        if i < m {
          if *arr2.get(i, j) < 0.0 {
            i = i + 1
          } else {
            i = 0;
            j = j + 1;
            break;
          }
        } else {
          return true
        }
      }
    } else {
      i = 0;
      j = j + 1;
    }
  }
  false
}


/* step 3 */

#[lr::sig(fn (m:usize{0<m}, n:usize{2<n}, arr2: &RMat<f32>[m,n]) -> usize{v: 0<v && v+1<n})]
pub fn enter_var(_m:usize, n:usize, arr2: &RMat<f32>) -> usize {
  let mut c  = *arr2.get(0, 1);
  let mut j  = 1;
  let mut j_ = 2;
  while j_ < n - 1 {
    // INV j+1 < n, j_ < n
    let c_ = *arr2.get(0, j_);
	  if c_ < c {
      j = j_;
      c = c_;
    }
    j_ += 1
  }
  j
}

/* step 4 */

#[lr::sig(fn(m:usize, n:usize, arr2: &RMat<f32>[m, n], j:usize{0 < j && j < n}, i0:usize{0 < i0 && i0 < m}, r0:f32) -> usize{v:0 < v && v < m})]
pub fn depart_var(m:usize, n:usize, arr2: &RMat<f32>, j:usize, i0:usize, r0:f32) -> usize {
  let mut i  = i0;
  let mut r  = r0;
  let mut i_ = i + 1;
  while i_ < m {
    let c_ = *arr2.get(i_, j);
    if 0.0 < c_ {
        let r_ = *arr2.get(i_, n-1) / c_;
        if r_ < r {
          i = i_;
          r = r_;
        }
        i_ += 1;
    } else {
      i_ += 1
    }
  }
  i
}



#[lr::sig(fn (m:usize{0 < m}, n:usize{0 < n}, arr2: &RMat<f32>[m, n], j: usize{0 < j && j < n}) -> usize{v:0 < v && v < m})]
pub fn init_ratio_i(m:usize, _n:usize, arr2: &RMat<f32>, j: usize) -> usize {
  let mut i = 1;
  while i < m {
    let c = *arr2.get(i, j);
    if 0.0 < c {
      return i
    }
    i += 1;
  }
  rmat::die() // abort ("init_ratio: negative coefficients!")
}

#[lr::sig(fn(m:usize{0 < m}, n:usize{0 < n}, arr2: &RMat<f32>[m, n],
             j: usize{0 < j && j < n}, i:usize{0 < i && i < m}
            ) -> f32)]
pub fn init_ratio_c(_m:usize, n:usize, arr2: &RMat<f32>, j: usize, i: usize) -> f32 {
  *arr2.get(i, j) / *arr2.get(i, n-1)
}

/* step 5 */

#[lr::sig(fn (m:usize, n:usize, arr2:&mut RMat<f32>[m,n], i:usize{0 < i && i < m}, j:usize{0 < j && j < n}) -> i32)]
fn row_op(m:usize, n:usize, arr2:&mut RMat<f32>, i:usize, j:usize) -> i32 {

  // norm(m, n, arr2, i, j);
  let c = *arr2.get(i, j);
  let mut j = 1;
  while j < n {
    *arr2.get_mut(i, j) /= c;
    j += 1;
  }

  // ro_op_aux3(m, n, arr2, i, j, 0)
  let mut i_ = 0;
  while i_ < m {
    if i_ != i {
      let c_ = *arr2.get(i_, j); //~ ERROR precondition might not hold
      let mut j = 1;
      while j < n {
        let cj  = *arr2.get(i, j);
        let cj_ = *arr2.get(i_, j);
        *arr2.get_mut(i_, j) = cj_ - cj * c_;
        j += 1
      }
    }
    i_ += 1
  }
  0
}

#[lr::sig(fn (m:usize{1 < m}, n:usize{2 < n}, arr2:&mut RMat<f32>[m, n]) -> i32)]
pub fn simplex(m:usize, n:usize, arr2:&mut RMat<f32>) -> i32 {
  while is_neg(arr2, m, n) {
    if unb1(m, n, arr2) {
      rmat::die();
      return 0
    } else {
      let j = enter_var(m, n, arr2);
      let i = init_ratio_i(m, n, arr2, j);
      let r = init_ratio_c(m, n, arr2, j, i);
      let i = depart_var(m, n, arr2, j, i, r);
      row_op(m, n, arr2, i, j);
    }
  }
  0
}

/*
(*
(* An implementation of the simplex method in DML *)

datatype 'a array2D with (nat,nat) =
  {m:nat,n:nat} A(m,n) of ('a array(n)) array(m) * int(m) * int(n)

fun('a) nRows (A (_, m, _)) = m
withtype {m:nat,n:nat} <> => 'a array2D(m,n) -> int(m)

fun('a) nCols (A (_, _, n)) = n
withtype {m:nat,n:nat} <> => 'a array2D(m,n) -> int(n)

(* step 1 *)

fun is_neg_aux (arr2, n, j) =
    if j < n - 1 then
	if sub2 (arr2, 0, j) <. 0.0 then true
	else is_neg_aux (arr2, n, j+1)
    else false
withtype {m:pos,n:pos,j:nat | j <= n} <n-j> =>
         (float array(n)) array(m) * int(n) * int(j) -> bool

fun is_neg (arr2, n) = is_neg_aux (arr2, n, 1)
withtype {m:pos,n:pos} <> => (float array(n)) array(m) * int(n) -> bool

(* step 2 *)

fun unb1 (arr2, m, n, i, j) =
    if j < n-1 then
	if sub2 (arr2, 0, j) <. 0.0 then unb2 (arr2, m, n, i+1, j)
	else unb1 (arr2, m, n, 0, j+1)
    else false
withtype {m:pos,n:pos,i:nat,j:nat | i < m, j <= n} <n-j, m-i> =>
         (float array(n)) array(m) * int (m) * int(n) * int(i) * int(j) -> bool

and unb2 (arr2, m, n, i, j) =
    if i < m then
	if sub2 (arr2, i, j) <. 0.0 then unb2 (arr2, m, n, i+1, j)
	else unb1 (arr2, m, n, 0, j+1)
    else true
withtype {m:pos,n:pos,i:nat,j:nat | i <= m, j < n} <n-j,m-i> =>
         (float array(n)) array(m) * int (m) * int(n) * int(i) * int(j) -> bool


(* step 3 *)

fun enter_var (arr2, n, j, c, j') =
    if j' < n-1 then
	let
	    val c' = sub2 (arr2, 0, j')
	in
	    if c' <. c then enter_var (arr2, n, j', c', j'+1)
	    else enter_var (arr2, n, j, c, j'+1)
	end
    else j
withtype {m:pos,n:pos,j:pos,j':pos | j+1 < n, j' < n} <n-j'> =>
         (float array(n)) array(m) * int(n) * int(j) * float * int(j') ->
	 [j:pos | j+1 < n] int(j)

(* step 4 *)

fun depart_var (arr2, m, n, j, i, r, i') =
    if i' < m then
	let
	    val c' = sub2 (arr2, i', j)
	in
	    if c' >. 0.0 then
		let
		    val r' = sub2(arr2, i', n-1) /. c'
		in
		    if r' <. r then depart_var(arr2, m, n, j, i', r', i'+1)
		    else depart_var (arr2, m, n, j, i, r, i'+1)
		end
	    else depart_var (arr2, m, n, j, i, r, i'+1)
	end
    else i
withtype {m:pos,n:pos,i:pos,i':pos,j:pos | i < m, i' <= m, j < n} <m-i'> =>
         (float array(n)) array(m) * int(m) * int(n) * int(j) * int(i) * float * int(i') ->
	 [i:pos | i < m] int(i)

fun init_ratio (arr2, m, n, j, i) =
  if i < m then
      let
	  val c = sub2 (arr2, i, j)
      in
	  if c >. 0.0 then (i, sub2 (arr2, i, n-1) /. c)
	  else init_ratio (arr2, m, n, j, i+1)
      end
  else abort ("init_ratio: negative coefficients!")
withtype {m:pos,n:pos,j:pos,i:pos | j < n, i <= m} <m-i> =>
         (float array(n)) array(m) * int(m) * int(n) * int(j) * int(i) ->
         [i:pos | i < m] int(i) * float

(* step 5 *)

fun norm_aux (arr2, n, i, c, j) =
  if j < n then
    let
        val _ = update2 (arr2, i, j, sub2 (arr2, i, j) /. c)
    in
        norm_aux (arr2, n, i, c, j+1)
    end
  else ()
withtype {m:pos,n:pos,i:pos,j:pos | i < m, j <= n} <n-j> =>
         (float array(n)) array(m) * int(n) * int(i) * float * int(j) -> unit

fun norm (arr2, n, i, j) =
  let
      val c = sub2 (arr2, i, j)
  in
      norm_aux (arr2, n, i, c, 1)
  end
withtype {m:pos,n:pos,i:pos,j:pos | i < m, j < n} <> =>
         (float array(n)) array(m) * int(n) * int(i) * int(j) -> unit

fun row_op_aux1 (arr2, n, i, i', c, j) =
  if j < n then
      let
	  val cj =  sub2 (arr2, i, j)
	  val cj' =  sub2 (arr2, i', j)
	  val _ = update2 (arr2, i', j, cj' -. cj *. c)
      in
	  row_op_aux1 (arr2, n, i, i', c, j+1)
      end
  else ()
withtype {m:pos,n:pos,i:pos,i':nat, j:pos | i < m, i' < m, j <= n} <n-j> =>
         (float array(n)) array(m) * int(n) * int(i) * int(i') * float * int(j) -> unit

fun row_op_aux2 (arr2, n, i, i', j) =
  let
      val c' = sub2 (arr2, i', j)
  in
      row_op_aux1 (arr2, n, i, i', c', 1)
  end
withtype {m:pos,n:pos,i:pos,i':nat, j:pos | i < m, i' < m, j < n} <> =>
         (float array(n)) array(m) * int(n) * int(i) * int(i') * int(j) -> unit

fun row_op_aux3 (arr2, m, n, i, j, i') =
  if i' < m then
     if i' <> i then
	 let
	     val _ = row_op_aux2(arr2, n, i, i', j)
	 in
	     row_op_aux3 (arr2, m, n, i, j, i'+1)
         end
     else row_op_aux3 (arr2, m, n, i, j, i'+1)
  else ()
withtype {m:pos,n:pos,i:pos,j:pos,i':nat | i < m, j < n, i' <= m} <m-i'> =>
         (float array(n)) array(m) * int(m) * int(n) * int(i) * int(j) * int(i') -> unit

fun row_op (arr2, m, n, i, j) =
    let
	val _ = norm (arr2, n, i, j)
    in
	row_op_aux3 (arr2, m, n, i, j, 0)
    end
withtype {m:pos,n:pos,i:pos,j:pos| i < m, j < n} <> =>
         (float array(n)) array(m) * int(m) * int(n) * int(i) * int(j) -> unit

fun simplex (arr2, m, n) =
    if is_neg (arr2, n) then
	if unb1 (arr2, m, n, 0, 1) then abort ("simplex: unbound solution!")
	else
	    let
		val j = enter_var (arr2, n, 1, sub2 (arr2, 0, 1), 2)
		val (i, r) = init_ratio (arr2, m, n, j, 1)
		val i = depart_var  (arr2, m, n, j, i, r, i+1)
		val _ = row_op (arr2, m, n, i, j)
	    in
		simplex (arr2, m, n)
	    end
    else ()
withtype {m:int,n:int | m > 1, n > 2}
         (float array(n)) array(m) * int(m) * int(n) -> unit

fun main (A (arr2, m, n)) =
  if m > 1 then
      if n > 2 then simplex (arr2, m, n)
      else abort ("too few columns")
  else abort ("too few rows")
withtype float array2D -> unit
*)
 */
