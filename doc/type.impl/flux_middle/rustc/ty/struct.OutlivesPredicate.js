(function() {var type_impls = {
"flux_middle":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#impl-Clone-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;</h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#174\">source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: &amp;Self)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#impl-Debug-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"type\" href=\"https://doc.rust-lang.org/nightly/core/fmt/type.Result.html\" title=\"type core::fmt::Result\">Result</a></h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Decodable%3C__D%3E-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#impl-Decodable%3C__D%3E-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T, __D: TyDecoder&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_serialize/serialize/trait.Decodable.html\" title=\"trait rustc_serialize::serialize::Decodable\">Decodable</a>&lt;__D&gt; for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_serialize/serialize/trait.Decodable.html\" title=\"trait rustc_serialize::serialize::Decodable\">Decodable</a>&lt;__D&gt;,</div></h3></section></summary><div class=\"impl-items\"><section id=\"method.decode\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#method.decode\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_serialize/serialize/trait.Decodable.html#tymethod.decode\" class=\"fn\">decode</a>(__decoder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut __D</a>) -&gt; Self</h4></section></div></details>","Decodable<__D>","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Encodable%3C__E%3E-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#impl-Encodable%3C__E%3E-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T, __E: TyEncoder&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_serialize/serialize/trait.Encodable.html\" title=\"trait rustc_serialize::serialize::Encodable\">Encodable</a>&lt;__E&gt; for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_serialize/serialize/trait.Encodable.html\" title=\"trait rustc_serialize::serialize::Encodable\">Encodable</a>&lt;__E&gt;,</div></h3></section></summary><div class=\"impl-items\"><section id=\"method.encode\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#method.encode\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_serialize/serialize/trait.Encodable.html#tymethod.encode\" class=\"fn\">encode</a>(&amp;self, __encoder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut __E</a>)</h4></section></div></details>","Encodable<__E>","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Hash-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#impl-Hash-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a> for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#method.hash\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\" class=\"fn\">hash</a>&lt;__H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>&gt;(&amp;self, state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut __H</a>)</h4></section></summary><div class='docblock'>Feeds this value into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash_slice\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.3.0\">1.3.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/hash/mod.rs.html#235-237\">source</a></span><a href=\"#method.hash_slice\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\" class=\"fn\">hash_slice</a>&lt;H&gt;(data: &amp;[Self], state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut H</a>)<div class=\"where\">where\n    H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>,\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Feeds a slice of this type into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\">Read more</a></div></details></div></details>","Hash","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PartialEq-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#impl-PartialEq-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html\" title=\"trait core::cmp::PartialEq\">PartialEq</a> for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.eq\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#method.eq\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#tymethod.eq\" class=\"fn\">eq</a>(&amp;self, other: &amp;<a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>self</code> and <code>other</code> values to be equal, and is used by <code>==</code>.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.ne\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#261\">source</a></span><a href=\"#method.ne\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialEq.html#method.ne\" class=\"fn\">ne</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>Tests for <code>!=</code>. The default implementation is almost always sufficient,\nand should not be overridden without very good reason.</div></details></div></details>","PartialEq","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-TypeFoldable-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#451-455\">source</a><a href=\"#impl-TypeFoldable-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeFoldable.html\" title=\"trait flux_middle::rty::fold::TypeFoldable\">TypeFoldable</a>&gt; <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeFoldable.html\" title=\"trait flux_middle::rty::fold::TypeFoldable\">TypeFoldable</a> for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;</h3></section></summary><div class=\"impl-items\"><section id=\"method.try_fold_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#452-454\">source</a><a href=\"#method.try_fold_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#tymethod.try_fold_with\" class=\"fn\">try_fold_with</a>&lt;F: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.FallibleTypeFolder.html\" title=\"trait flux_middle::rty::fold::FallibleTypeFolder\">FallibleTypeFolder</a>&gt;(\n    &amp;self,\n    folder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut F</a>,\n) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;Self, F::<a class=\"associatedtype\" href=\"flux_middle/rty/fold/trait.FallibleTypeFolder.html#associatedtype.Error\" title=\"type flux_middle::rty::fold::FallibleTypeFolder::Error\">Error</a>&gt;</h4></section><section id=\"method.fold_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#236-238\">source</a><a href=\"#method.fold_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.fold_with\" class=\"fn\">fold_with</a>&lt;F: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeFolder.html\" title=\"trait flux_middle::rty::fold::TypeFolder\">TypeFolder</a>&gt;(&amp;self, folder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut F</a>) -&gt; Self</h4></section><section id=\"method.normalize_projections\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#240-248\">source</a><a href=\"#method.normalize_projections\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.normalize_projections\" class=\"fn\">normalize_projections</a>&lt;'tcx&gt;(\n    &amp;self,\n    genv: <a class=\"struct\" href=\"flux_middle/global_env/struct.GlobalEnv.html\" title=\"struct flux_middle::global_env::GlobalEnv\">GlobalEnv</a>&lt;'_, 'tcx&gt;,\n    infcx: &amp;<a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_infer/infer/struct.InferCtxt.html\" title=\"struct rustc_infer::infer::InferCtxt\">InferCtxt</a>&lt;'tcx&gt;,\n    callsite_def_id: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_span/def_id/struct.DefId.html\" title=\"struct rustc_span::def_id::DefId\">DefId</a>,\n) -&gt; <a class=\"type\" href=\"flux_middle/queries/type.QueryResult.html\" title=\"type flux_middle::queries::QueryResult\">QueryResult</a>&lt;Self&gt;</h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.normalize\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#251-253\">source</a><a href=\"#method.normalize\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.normalize\" class=\"fn\">normalize</a>(&amp;self, defns: &amp;<a class=\"struct\" href=\"flux_middle/rty/normalize/struct.SpecFuncDefns.html\" title=\"struct flux_middle::rty::normalize::SpecFuncDefns\">SpecFuncDefns</a>) -&gt; Self</h4></section></summary><div class='docblock'>Normalize expressions by applying beta reductions for tuples and lambda abstractions.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.replace_holes\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#262-286\">source</a><a href=\"#method.replace_holes\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.replace_holes\" class=\"fn\">replace_holes</a>(&amp;self, f: impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.FnMut.html\" title=\"trait core::ops::function::FnMut\">FnMut</a>(&amp;[<a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;<a class=\"enum\" href=\"flux_middle/rty/enum.Sort.html\" title=\"enum flux_middle::rty::Sort\">Sort</a>&gt;], <a class=\"enum\" href=\"flux_middle/rty/expr/enum.HoleKind.html\" title=\"enum flux_middle::rty::expr::HoleKind\">HoleKind</a>) -&gt; <a class=\"type\" href=\"flux_middle/rty/expr/type.Expr.html\" title=\"type flux_middle::rty::expr::Expr\">Expr</a>) -&gt; Self</h4></section></summary><div class='docblock'>Replaces all <a href=\"flux_middle/rty/expr/enum.ExprKind.html#variant.Hole\" title=\"variant flux_middle::rty::expr::ExprKind::Hole\">holes</a> with the result of calling a closure. The closure takes a list with\nall the <em>layers</em> of <a href=\"flux_middle/rty/struct.Binder.html\" title=\"struct flux_middle::rty::Binder\">bound</a> variables at the point the hole was found. Each layer corresponds\nto the list of sorts bound at that level. The list is ordered from outermost to innermost\nbinder, i.e., the last element is the binder closest to the hole.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.with_holes\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#293-307\">source</a><a href=\"#method.with_holes\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.with_holes\" class=\"fn\">with_holes</a>(&amp;self) -&gt; Self</h4></section></summary><div class='docblock'>Remove all refinements and turn each underlying <a href=\"flux_middle/rty/enum.BaseTy.html\" title=\"enum flux_middle::rty::BaseTy\"><code>BaseTy</code></a> into a <a href=\"flux_middle/rty/enum.TyKind.html#variant.Exists\" title=\"variant flux_middle::rty::TyKind::Exists\"><code>TyKind::Exists</code></a> with a\n<a href=\"flux_middle/rty/enum.TyKind.html#variant.Constr\" title=\"variant flux_middle::rty::TyKind::Constr\"><code>TyKind::Constr</code></a> and a <a href=\"flux_middle/rty/expr/enum.ExprKind.html#variant.Hole\" title=\"variant flux_middle::rty::expr::ExprKind::Hole\"><code>hole</code></a>. For example, <code>Vec&lt;{v. i32[v] | v &gt; 0}&gt;[n]</code> becomes\n<code>{n. Vec&lt;{v. i32[v] | *}&gt;[n] | *}</code>.</div></details><section id=\"method.replace_evars\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#309-312\">source</a><a href=\"#method.replace_evars\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.replace_evars\" class=\"fn\">replace_evars</a>(&amp;self, evars: &amp;<a class=\"struct\" href=\"flux_middle/rty/evars/struct.EVarSol.html\" title=\"struct flux_middle::rty::evars::EVarSol\">EVarSol</a>) -&gt; Self</h4></section><section id=\"method.shift_in_escaping\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#314-352\">source</a><a href=\"#method.shift_in_escaping\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.shift_in_escaping\" class=\"fn\">shift_in_escaping</a>(&amp;self, amount: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>) -&gt; Self</h4></section><section id=\"method.shift_out_escaping\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#354-389\">source</a><a href=\"#method.shift_out_escaping\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.shift_out_escaping\" class=\"fn\">shift_out_escaping</a>(&amp;self, amount: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>) -&gt; Self</h4></section></div></details>","TypeFoldable","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-TypeVisitable-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#444-449\">source</a><a href=\"#impl-TypeVisitable-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeVisitable.html\" title=\"trait flux_middle::rty::fold::TypeVisitable\">TypeVisitable</a>&gt; <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeVisitable.html\" title=\"trait flux_middle::rty::fold::TypeVisitable\">TypeVisitable</a> for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;</h3></section></summary><div class=\"impl-items\"><section id=\"method.visit_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#445-448\">source</a><a href=\"#method.visit_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeVisitable.html#tymethod.visit_with\" class=\"fn\">visit_with</a>&lt;V: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeVisitor.html\" title=\"trait flux_middle::rty::fold::TypeVisitor\">TypeVisitor</a>&gt;(&amp;self, visitor: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut V</a>) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/ops/control_flow/enum.ControlFlow.html\" title=\"enum core::ops::control_flow::ControlFlow\">ControlFlow</a>&lt;V::<a class=\"associatedtype\" href=\"flux_middle/rty/fold/trait.TypeVisitor.html#associatedtype.BreakTy\" title=\"type flux_middle::rty::fold::TypeVisitor::BreakTy\">BreakTy</a>&gt;</h4></section><section id=\"method.has_escaping_bvars\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#177-209\">source</a><a href=\"#method.has_escaping_bvars\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeVisitable.html#method.has_escaping_bvars\" class=\"fn\">has_escaping_bvars</a>(&amp;self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.fvars\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#213-226\">source</a><a href=\"#method.fvars\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeVisitable.html#method.fvars\" class=\"fn\">fvars</a>(&amp;self) -&gt; FxHashSet&lt;<a class=\"struct\" href=\"flux_middle/rty/expr/struct.Name.html\" title=\"struct flux_middle::rty::expr::Name\">Name</a>&gt;</h4></section></summary><div class='docblock'>Returns the set of all free variables.\nFor example, <code>Vec&lt;i32[n]&gt;{v : v &gt; m}</code> returns <code>{n, m}</code>.</div></details></div></details>","TypeVisitable","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"],["<section id=\"impl-Eq-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#impl-Eq-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Eq.html\" title=\"trait core::cmp::Eq\">Eq</a> for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;</h3></section>","Eq","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"],["<section id=\"impl-StructuralPartialEq-for-OutlivesPredicate%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty.rs.html#89\">source</a><a href=\"#impl-StructuralPartialEq-for-OutlivesPredicate%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.StructuralPartialEq.html\" title=\"trait core::marker::StructuralPartialEq\">StructuralPartialEq</a> for <a class=\"struct\" href=\"flux_middle/rustc/ty/struct.OutlivesPredicate.html\" title=\"struct flux_middle::rustc::ty::OutlivesPredicate\">OutlivesPredicate</a>&lt;T&gt;</h3></section>","StructuralPartialEq","flux_middle::rty::TypeOutlivesPredicate","flux_middle::rustc::ty::TypeOutlivesPredicate"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()