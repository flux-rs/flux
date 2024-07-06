(function() {var type_impls = {
"flux_middle":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Default-for-Interned%3C%5BT%5D%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#265-272\">source</a><a href=\"#impl-Default-for-Interned%3C%5BT%5D%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>: <a class=\"trait\" href=\"flux_middle/intern/trait.Internable.html\" title=\"trait flux_middle::intern::Internable\">Internable</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.default\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#269-271\">source</a><a href=\"#method.default\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html#tymethod.default\" class=\"fn\">default</a>() -&gt; Self</h4></section></summary><div class='docblock'>Returns the “default value” for a type. <a href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html#tymethod.default\">Read more</a></div></details></div></details>","Default","flux_middle::rty::PolyVariants","flux_middle::rty::RefineArgs","flux_middle::rty::GenericArgs","flux_middle::rustc::ty::GenericArgs"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-FromIterator%3CT%3E-for-Interned%3C%5BT%5D%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#343-350\">source</a><a href=\"#impl-FromIterator%3CT%3E-for-Interned%3C%5BT%5D%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/iter/traits/collect/trait.FromIterator.html\" title=\"trait core::iter::traits::collect::FromIterator\">FromIterator</a>&lt;T&gt; for <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>: <a class=\"trait\" href=\"flux_middle/intern/trait.Internable.html\" title=\"trait flux_middle::intern::Internable\">Internable</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.from_iter\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#347-349\">source</a><a href=\"#method.from_iter\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/iter/traits/collect/trait.FromIterator.html#tymethod.from_iter\" class=\"fn\">from_iter</a>&lt;I: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/iter/traits/collect/trait.IntoIterator.html\" title=\"trait core::iter::traits::collect::IntoIterator\">IntoIterator</a>&lt;Item = T&gt;&gt;(iter: I) -&gt; Self</h4></section></summary><div class='docblock'>Creates a value from an iterator. <a href=\"https://doc.rust-lang.org/nightly/core/iter/traits/collect/trait.FromIterator.html#tymethod.from_iter\">Read more</a></div></details></div></details>","FromIterator<T>","flux_middle::rty::PolyVariants","flux_middle::rty::RefineArgs","flux_middle::rty::GenericArgs","flux_middle::rustc::ty::GenericArgs"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Interned%3C%5BT%5D%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#291-331\">source</a><a href=\"#impl-Interned%3C%5BT%5D%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>: <a class=\"trait\" href=\"flux_middle/intern/trait.Internable.html\" title=\"trait flux_middle::intern::Internable\">Internable</a>,</div></h3></section></summary><div class=\"impl-items\"><section id=\"method.list_with\" class=\"method\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#295-314\">source</a><h4 class=\"code-header\">fn <a href=\"flux_middle/intern/type.List.html#tymethod.list_with\" class=\"fn\">list_with</a>&lt;S&gt;(obj: S, to_arc: impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.FnOnce.html\" title=\"trait core::ops::function::FnOnce\">FnOnce</a>(S) -&gt; <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/sync/struct.Arc.html\" title=\"struct alloc::sync::Arc\">Arc</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>&gt;) -&gt; <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    S: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/borrow/trait.Borrow.html\" title=\"trait core::borrow::Borrow\">Borrow</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>&gt;,</div></h4></section><section id=\"method.from_vec\" class=\"method\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#316-318\">source</a><h4 class=\"code-header\">pub fn <a href=\"flux_middle/intern/type.List.html#tymethod.from_vec\" class=\"fn\">from_vec</a>(vec: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;T&gt;) -&gt; <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;</h4></section><section id=\"method.from_arr\" class=\"method\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#320-322\">source</a><h4 class=\"code-header\">pub fn <a href=\"flux_middle/intern/type.List.html#tymethod.from_arr\" class=\"fn\">from_arr</a>&lt;const N: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>&gt;(arr: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">[T; N]</a>) -&gt; <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;</h4></section><section id=\"method.empty\" class=\"method\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#324-326\">source</a><h4 class=\"code-header\">pub fn <a href=\"flux_middle/intern/type.List.html#tymethod.empty\" class=\"fn\">empty</a>() -&gt; <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;</h4></section><section id=\"method.singleton\" class=\"method\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#328-330\">source</a><h4 class=\"code-header\">pub fn <a href=\"flux_middle/intern/type.List.html#tymethod.singleton\" class=\"fn\">singleton</a>(x: T) -&gt; <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;</h4></section></div></details>",0,"flux_middle::rty::PolyVariants","flux_middle::rty::RefineArgs","flux_middle::rty::GenericArgs","flux_middle::rustc::ty::GenericArgs"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Interned%3C%5BT%5D%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#333-341\">source</a><a href=\"#impl-Interned%3C%5BT%5D%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a>,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>: <a class=\"trait\" href=\"flux_middle/intern/trait.Internable.html\" title=\"trait flux_middle::intern::Internable\">Internable</a>,</div></h3></section></summary><div class=\"impl-items\"><section id=\"method.from_slice\" class=\"method\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#338-340\">source</a><h4 class=\"code-header\">pub fn <a href=\"flux_middle/intern/type.List.html#tymethod.from_slice\" class=\"fn\">from_slice</a>(slice: &amp;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>) -&gt; <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;</h4></section></div></details>",0,"flux_middle::rty::PolyVariants","flux_middle::rty::RefineArgs","flux_middle::rty::GenericArgs","flux_middle::rustc::ty::GenericArgs"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Ord-for-Interned%3C%5BT%5D%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#475-483\">source</a><a href=\"#impl-Ord-for-Interned%3C%5BT%5D%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a> for <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html\" title=\"trait core::cmp::Ord\">Ord</a>,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>: <a class=\"trait\" href=\"flux_middle/intern/trait.Internable.html\" title=\"trait flux_middle::intern::Internable\">Internable</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.cmp\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#480-482\">source</a><a href=\"#method.cmp\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html#tymethod.cmp\" class=\"fn\">cmp</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Self</a>) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/cmp/enum.Ordering.html\" title=\"enum core::cmp::Ordering\">Ordering</a></h4></section></summary><div class='docblock'>This method returns an <a href=\"https://doc.rust-lang.org/nightly/core/cmp/enum.Ordering.html\" title=\"enum core::cmp::Ordering\"><code>Ordering</code></a> between <code>self</code> and <code>other</code>. <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html#tymethod.cmp\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.max\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.21.0\">1.21.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#855-857\">source</a></span><a href=\"#method.max\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html#method.max\" class=\"fn\">max</a>(self, other: Self) -&gt; Self<div class=\"where\">where\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Compares and returns the maximum of two values. <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html#method.max\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.min\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.21.0\">1.21.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#876-878\">source</a></span><a href=\"#method.min\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html#method.min\" class=\"fn\">min</a>(self, other: Self) -&gt; Self<div class=\"where\">where\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Compares and returns the minimum of two values. <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html#method.min\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clamp\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.50.0\">1.50.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#902-905\">source</a></span><a href=\"#method.clamp\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html#method.clamp\" class=\"fn\">clamp</a>(self, min: Self, max: Self) -&gt; Self<div class=\"where\">where\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html\" title=\"trait core::cmp::PartialOrd\">PartialOrd</a>,</div></h4></section></summary><div class='docblock'>Restrict a value to a certain interval. <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.Ord.html#method.clamp\">Read more</a></div></details></div></details>","Ord","flux_middle::rty::PolyVariants","flux_middle::rty::RefineArgs","flux_middle::rty::GenericArgs","flux_middle::rustc::ty::GenericArgs"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-PartialOrd-for-Interned%3C%5BT%5D%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#465-473\">source</a><a href=\"#impl-PartialOrd-for-Interned%3C%5BT%5D%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html\" title=\"trait core::cmp::PartialOrd\">PartialOrd</a> for <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html\" title=\"trait core::cmp::PartialOrd\">PartialOrd</a>,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>: <a class=\"trait\" href=\"flux_middle/intern/trait.Internable.html\" title=\"trait flux_middle::intern::Internable\">Internable</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.partial_cmp\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/intern.rs.html#470-472\">source</a><a href=\"#method.partial_cmp\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#tymethod.partial_cmp\" class=\"fn\">partial_cmp</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Self</a>) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/option/enum.Option.html\" title=\"enum core::option::Option\">Option</a>&lt;<a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/cmp/enum.Ordering.html\" title=\"enum core::cmp::Ordering\">Ordering</a>&gt;</h4></section></summary><div class='docblock'>This method returns an ordering between <code>self</code> and <code>other</code> values if one exists. <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#tymethod.partial_cmp\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.lt\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#1179\">source</a></span><a href=\"#method.lt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#method.lt\" class=\"fn\">lt</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests less than (for <code>self</code> and <code>other</code>) and is used by the <code>&lt;</code> operator. <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#method.lt\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.le\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#1197\">source</a></span><a href=\"#method.le\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#method.le\" class=\"fn\">le</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests less than or equal to (for <code>self</code> and <code>other</code>) and is used by the <code>&lt;=</code>\noperator. <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#method.le\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.gt\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#1214\">source</a></span><a href=\"#method.gt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#method.gt\" class=\"fn\">gt</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests greater than (for <code>self</code> and <code>other</code>) and is used by the <code>&gt;</code> operator. <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#method.gt\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.ge\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/cmp.rs.html#1232\">source</a></span><a href=\"#method.ge\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#method.ge\" class=\"fn\">ge</a>(&amp;self, other: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Rhs</a>) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section></summary><div class='docblock'>This method tests greater than or equal to (for <code>self</code> and <code>other</code>) and is used by the <code>&gt;=</code>\noperator. <a href=\"https://doc.rust-lang.org/nightly/core/cmp/trait.PartialOrd.html#method.ge\">Read more</a></div></details></div></details>","PartialOrd","flux_middle::rty::PolyVariants","flux_middle::rty::RefineArgs","flux_middle::rty::GenericArgs","flux_middle::rustc::ty::GenericArgs"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Subst-for-Interned%3C%5BT%5D%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty/subst.rs.html#87-95\">source</a><a href=\"#impl-Subst-for-Interned%3C%5BT%5D%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"flux_middle/rustc/ty/subst/trait.Subst.html\" title=\"trait flux_middle::rustc::ty::subst::Subst\">Subst</a> for <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"flux_middle/rustc/ty/subst/trait.Subst.html\" title=\"trait flux_middle::rustc::ty::subst::Subst\">Subst</a>,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>: <a class=\"trait\" href=\"flux_middle/intern/trait.Internable.html\" title=\"trait flux_middle::intern::Internable\">Internable</a>,</div></h3></section></summary><div class=\"impl-items\"><section id=\"method.subst\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rustc/ty/subst.rs.html#92-94\">source</a><a href=\"#method.subst\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rustc/ty/subst/trait.Subst.html#tymethod.subst\" class=\"fn\">subst</a>(&amp;self, args: &amp;[<a class=\"enum\" href=\"flux_middle/rustc/ty/enum.GenericArg.html\" title=\"enum flux_middle::rustc::ty::GenericArg\">GenericArg</a>]) -&gt; Self</h4></section></div></details>","Subst","flux_middle::rty::PolyVariants","flux_middle::rty::RefineArgs","flux_middle::rty::GenericArgs","flux_middle::rustc::ty::GenericArgs"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-TypeFoldable-for-Interned%3C%5BT%5D%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#1271-1279\">source</a><a href=\"#impl-TypeFoldable-for-Interned%3C%5BT%5D%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeFoldable.html\" title=\"trait flux_middle::rty::fold::TypeFoldable\">TypeFoldable</a> for <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeFoldable.html\" title=\"trait flux_middle::rty::fold::TypeFoldable\">TypeFoldable</a>,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>: <a class=\"trait\" href=\"flux_middle/intern/trait.Internable.html\" title=\"trait flux_middle::intern::Internable\">Internable</a>,</div></h3></section></summary><div class=\"impl-items\"><section id=\"method.try_fold_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#1276-1278\">source</a><a href=\"#method.try_fold_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#tymethod.try_fold_with\" class=\"fn\">try_fold_with</a>&lt;F: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.FallibleTypeFolder.html\" title=\"trait flux_middle::rty::fold::FallibleTypeFolder\">FallibleTypeFolder</a>&gt;(\n    &amp;self,\n    folder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut F</a>,\n) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;Self, F::<a class=\"associatedtype\" href=\"flux_middle/rty/fold/trait.FallibleTypeFolder.html#associatedtype.Error\" title=\"type flux_middle::rty::fold::FallibleTypeFolder::Error\">Error</a>&gt;</h4></section><section id=\"method.fold_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#231-233\">source</a><a href=\"#method.fold_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.fold_with\" class=\"fn\">fold_with</a>&lt;F: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeFolder.html\" title=\"trait flux_middle::rty::fold::TypeFolder\">TypeFolder</a>&gt;(&amp;self, folder: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut F</a>) -&gt; Self</h4></section><section id=\"method.normalize_projections\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#235-245\">source</a><a href=\"#method.normalize_projections\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.normalize_projections\" class=\"fn\">normalize_projections</a>&lt;'tcx&gt;(\n    &amp;self,\n    genv: <a class=\"struct\" href=\"flux_middle/global_env/struct.GlobalEnv.html\" title=\"struct flux_middle::global_env::GlobalEnv\">GlobalEnv</a>&lt;'_, 'tcx&gt;,\n    infcx: &amp;<a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_infer/infer/struct.InferCtxt.html\" title=\"struct rustc_infer::infer::InferCtxt\">InferCtxt</a>&lt;'tcx&gt;,\n    callsite_def_id: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/nightly-rustc/rustc_span/def_id/struct.DefId.html\" title=\"struct rustc_span::def_id::DefId\">DefId</a>,\n    refine_params: &amp;[<a class=\"type\" href=\"flux_middle/rty/expr/type.Expr.html\" title=\"type flux_middle::rty::expr::Expr\">Expr</a>],\n) -&gt; <a class=\"type\" href=\"flux_middle/queries/type.QueryResult.html\" title=\"type flux_middle::queries::QueryResult\">QueryResult</a>&lt;Self&gt;</h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.normalize\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#248-250\">source</a><a href=\"#method.normalize\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.normalize\" class=\"fn\">normalize</a>(&amp;self, defns: &amp;<a class=\"struct\" href=\"flux_middle/rty/normalize/struct.SpecFuncDefns.html\" title=\"struct flux_middle::rty::normalize::SpecFuncDefns\">SpecFuncDefns</a>) -&gt; Self</h4></section></summary><div class='docblock'>Normalize expressions by applying beta reductions for tuples and lambda abstractions.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.replace_holes\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#259-283\">source</a><a href=\"#method.replace_holes\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.replace_holes\" class=\"fn\">replace_holes</a>(&amp;self, f: impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/function/trait.FnMut.html\" title=\"trait core::ops::function::FnMut\">FnMut</a>(&amp;[<a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;<a class=\"enum\" href=\"flux_middle/rty/enum.Sort.html\" title=\"enum flux_middle::rty::Sort\">Sort</a>&gt;], <a class=\"enum\" href=\"flux_middle/rty/expr/enum.HoleKind.html\" title=\"enum flux_middle::rty::expr::HoleKind\">HoleKind</a>) -&gt; <a class=\"type\" href=\"flux_middle/rty/expr/type.Expr.html\" title=\"type flux_middle::rty::expr::Expr\">Expr</a>) -&gt; Self</h4></section></summary><div class='docblock'>Replaces all <a href=\"flux_middle/rty/expr/enum.ExprKind.html#variant.Hole\" title=\"variant flux_middle::rty::expr::ExprKind::Hole\">holes</a> with the result of calling a closure. The closure takes a list with\nall the <em>layers</em> of <a href=\"flux_middle/rty/struct.Binder.html\" title=\"struct flux_middle::rty::Binder\">bound</a> variables at the point the hole was found. Each layer corresponds\nto the list of sorts bound at that level. The list is ordered from outermost to innermost\nbinder, i.e., the last element is the binder closest to the hole.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.with_holes\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#290-317\">source</a><a href=\"#method.with_holes\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.with_holes\" class=\"fn\">with_holes</a>(&amp;self) -&gt; Self</h4></section></summary><div class='docblock'>Turns each <a href=\"flux_middle/rty/enum.TyKind.html#variant.Indexed\" title=\"variant flux_middle::rty::TyKind::Indexed\"><code>TyKind::Indexed</code></a> into a <a href=\"flux_middle/rty/enum.TyKind.html#variant.Exists\" title=\"variant flux_middle::rty::TyKind::Exists\"><code>TyKind::Exists</code></a> with a <a href=\"flux_middle/rty/enum.TyKind.html#variant.Constr\" title=\"variant flux_middle::rty::TyKind::Constr\"><code>TyKind::Constr</code></a> and a\n<a href=\"flux_middle/rty/expr/enum.ExprKind.html#variant.Hole\" title=\"variant flux_middle::rty::expr::ExprKind::Hole\"><code>hole</code></a>. It also replaces all existing predicates with a <a href=\"flux_middle/rty/expr/enum.ExprKind.html#variant.Hole\" title=\"variant flux_middle::rty::expr::ExprKind::Hole\"><code>hole</code></a>.\nFor example, <code>Vec&lt;{v. i32[v] | v &gt; 0}&gt;[n]</code> becomes <code>{n. Vec&lt;{v. i32[v] | *}&gt;[n] | *}</code>.</div></details><section id=\"method.replace_evars\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#319-322\">source</a><a href=\"#method.replace_evars\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.replace_evars\" class=\"fn\">replace_evars</a>(&amp;self, evars: &amp;<a class=\"struct\" href=\"flux_middle/rty/evars/struct.EVarSol.html\" title=\"struct flux_middle::rty::evars::EVarSol\">EVarSol</a>) -&gt; Self</h4></section><section id=\"method.shift_in_escaping\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#324-362\">source</a><a href=\"#method.shift_in_escaping\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.shift_in_escaping\" class=\"fn\">shift_in_escaping</a>(&amp;self, amount: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>) -&gt; Self</h4></section><section id=\"method.shift_out_escaping\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#364-399\">source</a><a href=\"#method.shift_out_escaping\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeFoldable.html#method.shift_out_escaping\" class=\"fn\">shift_out_escaping</a>(&amp;self, amount: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>) -&gt; Self</h4></section></div></details>","TypeFoldable","flux_middle::rty::PolyVariants","flux_middle::rty::RefineArgs","flux_middle::rty::GenericArgs","flux_middle::rustc::ty::GenericArgs"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-TypeVisitable-for-Interned%3C%5BT%5D%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#1261-1269\">source</a><a href=\"#impl-TypeVisitable-for-Interned%3C%5BT%5D%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeVisitable.html\" title=\"trait flux_middle::rty::fold::TypeVisitable\">TypeVisitable</a> for <a class=\"type\" href=\"flux_middle/intern/type.List.html\" title=\"type flux_middle::intern::List\">List</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeVisitable.html\" title=\"trait flux_middle::rty::fold::TypeVisitable\">TypeVisitable</a>,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.slice.html\">[T]</a>: <a class=\"trait\" href=\"flux_middle/intern/trait.Internable.html\" title=\"trait flux_middle::intern::Internable\">Internable</a>,</div></h3></section></summary><div class=\"impl-items\"><section id=\"method.visit_with\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#1266-1268\">source</a><a href=\"#method.visit_with\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeVisitable.html#tymethod.visit_with\" class=\"fn\">visit_with</a>&lt;V: <a class=\"trait\" href=\"flux_middle/rty/fold/trait.TypeVisitor.html\" title=\"trait flux_middle::rty::fold::TypeVisitor\">TypeVisitor</a>&gt;(&amp;self, visitor: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut V</a>) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/ops/control_flow/enum.ControlFlow.html\" title=\"enum core::ops::control_flow::ControlFlow\">ControlFlow</a>&lt;V::<a class=\"associatedtype\" href=\"flux_middle/rty/fold/trait.TypeVisitor.html#associatedtype.BreakTy\" title=\"type flux_middle::rty::fold::TypeVisitor::BreakTy\">BreakTy</a>&gt;</h4></section><section id=\"method.has_escaping_bvars\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#172-204\">source</a><a href=\"#method.has_escaping_bvars\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeVisitable.html#method.has_escaping_bvars\" class=\"fn\">has_escaping_bvars</a>(&amp;self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a></h4></section><details class=\"toggle method-toggle\" open><summary><section id=\"method.fvars\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_middle/rty/fold.rs.html#208-221\">source</a><a href=\"#method.fvars\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"flux_middle/rty/fold/trait.TypeVisitable.html#method.fvars\" class=\"fn\">fvars</a>(&amp;self) -&gt; FxHashSet&lt;<a class=\"struct\" href=\"flux_middle/rty/expr/struct.Name.html\" title=\"struct flux_middle::rty::expr::Name\">Name</a>&gt;</h4></section></summary><div class='docblock'>Returns the set of all free variables.\nFor example, <code>Vec&lt;i32[n]&gt;{v : v &gt; m}</code> returns <code>{n, m}</code>.</div></details></div></details>","TypeVisitable","flux_middle::rty::PolyVariants","flux_middle::rty::RefineArgs","flux_middle::rty::GenericArgs","flux_middle::rustc::ty::GenericArgs"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()