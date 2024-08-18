(function() {var type_impls = {
"flux_infer":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Display-for-KVar%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_fixpoint/lib.rs.html#233\">source</a><a href=\"#impl-Display-for-KVar%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html\" title=\"trait core::fmt::Display\">Display</a> for <a class=\"struct\" href=\"flux_fixpoint/struct.KVar.html\" title=\"struct flux_fixpoint::KVar\">KVar</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"flux_fixpoint/trait.Types.html\" title=\"trait flux_fixpoint::Types\">Types</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_fixpoint/lib.rs.html#234\">source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"enum\" href=\"https://doc.rust-lang.org/nightly/core/result/enum.Result.html\" title=\"enum core::result::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>, <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Error.html\" title=\"struct core::fmt::Error\">Error</a>&gt;</h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Display.html#tymethod.fmt\">Read more</a></div></details></div></details>","Display","flux_infer::fixpoint_encoding::fixpoint::fixpoint_generated::KVar"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Hash-for-KVar%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_fixpoint/lib.rs.html#128\">source</a><a href=\"#impl-Hash-for-KVar%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html\" title=\"trait core::hash::Hash\">Hash</a> for <a class=\"struct\" href=\"flux_fixpoint/struct.KVar.html\" title=\"struct flux_fixpoint::KVar\">KVar</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"flux_fixpoint/trait.Types.html\" title=\"trait flux_fixpoint::Types\">Types</a>,</div></h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/flux_fixpoint/lib.rs.html#128\">source</a><a href=\"#method.hash\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\" class=\"fn\">hash</a>&lt;__H&gt;(&amp;self, __state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut __H</a>)<div class=\"where\">where\n    __H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>,</div></h4></section></summary><div class='docblock'>Feeds this value into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#tymethod.hash\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.hash_slice\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.3.0\">1.3.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/hash/mod.rs.html#235-237\">source</a></span><a href=\"#method.hash_slice\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\" class=\"fn\">hash_slice</a>&lt;H&gt;(data: &amp;[Self], state: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut H</a>)<div class=\"where\">where\n    H: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\">Hasher</a>,\n    Self: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>,</div></h4></section></summary><div class='docblock'>Feeds a slice of this type into the given <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hasher.html\" title=\"trait core::hash::Hasher\"><code>Hasher</code></a>. <a href=\"https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html#method.hash_slice\">Read more</a></div></details></div></details>","Hash","flux_infer::fixpoint_encoding::fixpoint::fixpoint_generated::KVar"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-KVar%3CT%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/flux_fixpoint/lib.rs.html#190\">source</a><a href=\"#impl-KVar%3CT%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;T&gt; <a class=\"struct\" href=\"flux_fixpoint/struct.KVar.html\" title=\"struct flux_fixpoint::KVar\">KVar</a>&lt;T&gt;<div class=\"where\">where\n    T: <a class=\"trait\" href=\"flux_fixpoint/trait.Types.html\" title=\"trait flux_fixpoint::Types\">Types</a>,</div></h3></section></summary><div class=\"impl-items\"><section id=\"method.new\" class=\"method\"><a class=\"src rightside\" href=\"src/flux_fixpoint/lib.rs.html#191\">source</a><h4 class=\"code-header\">pub fn <a href=\"flux_fixpoint/struct.KVar.html#tymethod.new\" class=\"fn\">new</a>(\n    kvid: &lt;T as <a class=\"trait\" href=\"flux_fixpoint/trait.Types.html\" title=\"trait flux_fixpoint::Types\">Types</a>&gt;::<a class=\"associatedtype\" href=\"flux_fixpoint/trait.Types.html#associatedtype.KVar\" title=\"type flux_fixpoint::Types::KVar\">KVar</a>,\n    sorts: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/vec/struct.Vec.html\" title=\"struct alloc::vec::Vec\">Vec</a>&lt;<a class=\"enum\" href=\"flux_fixpoint/constraint/enum.Sort.html\" title=\"enum flux_fixpoint::constraint::Sort\">Sort</a>&lt;T&gt;&gt;,\n    comment: <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/alloc/string/struct.String.html\" title=\"struct alloc::string::String\">String</a>,\n) -&gt; <a class=\"struct\" href=\"flux_fixpoint/struct.KVar.html\" title=\"struct flux_fixpoint::KVar\">KVar</a>&lt;T&gt;</h4></section></div></details>",0,"flux_infer::fixpoint_encoding::fixpoint::fixpoint_generated::KVar"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()