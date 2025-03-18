searchState.loadedDescShard("flux_syntax", 0, "Contains the error value\nContains the success value\nAdvances the underlying cursor to the next token\nAdvances the underlying cursor by the requested number of …\nLooks at the next token and advances the cursor if it …\nLooks at the next two tokens advacing the cursor if there…\nReturns the token (and span) at the requested position.\nIf the next token matches the requested type of token …\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nLooks at the next token in the underlying cursor to …\nLooks at the next two tokens\nLooks at the next three tokens\nLooks whether the next token matches a binary operation. …\n<code>{ ... }</code>\n<code>[ ... ]</code>\nDescribes how a sequence of token trees is delimited. …\n<code>∅ ... ∅</code> An invisible delimiter, that may, for example, …\nA literal token.\n<code>( ... )</code>\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the highest byte position the cursor has yielded. …\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nReturns the starting byte position of the next token\n&amp;&amp;\nA peekable struct that matches any identifier\nA peekable struct that matches any literal\n&amp;\n|\n^\n== != &lt; &gt; &lt;= &gt;=\n&lt;=&gt;\n=&gt;\n||\nA trait for testing whether a single token matches some …\n/ %\n&lt;&lt; &gt;&gt;\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\n⟨asyncness⟩ := async?\n⟨atom⟩ := ⟨if_expr⟩ | ⟨lit⟩ | ( ⟨expr⟩ ) | …\n⟨base_sort⟩ := bitvec &lt; ⟨u32⟩ &gt; | ⟨sort_path⟩ &lt;…\n⟨block_expr⟩ := { ⟨expr⟩ }\n⟨bounded_quant⟩ := forall ⟨refine_param⟩ in …\n⟨bty⟩ { ⟨ident⟩ : ⟨expr⟩ }\n⟨bty⟩ [ ⟨refine_arg⟩,* ] |  ⟨bty⟩ { …\n⟨constructor_arg⟩ :=  ⟨ident⟩ : ⟨expr⟩ |  ..\n⟨ensures_clause⟩ :=  ⟨ident⟩ : ⟨ty⟩ |  …\n⟨epath⟩ := ⟨ident⟩ ⟨ :: ⟨ident⟩ ⟩*\n⟨fields⟩ := ( ⟨ty⟩,* ) | { ⟨ty⟩,* }\n⟨fn_input⟩ := ⟨ident⟩ : &amp;strg ⟨ty⟩ | …\n⟨fn_ret⟩ := ⟨ -&gt; ⟨ty⟩ ⟩?\n⟨fn_sig⟩ := ⟨asyncness⟩ fn ⟨ident⟩? ⟨ [ …\n{ ⟨refine_param⟩ ⟨,⟨refine_param⟩⟩* . ⟨ty⟩ …\n⟨generic_arg⟩ := ⟨ty⟩ | ⟨ident⟩ = ⟨ty⟩\n⟨if_expr⟩ := if ⟨cond⟩ ⟨block_expr⟩ ⟨ else …\n⟨impl_assoc_reft⟩ := fn ⟨ident⟩ ( …\n⟨lit⟩ := “a Rust literal like an integer or a boolean…\n⟨ensures⟩ := ⟨ensures ⟨ensures_clause⟩,*⟩?\n⟨mode⟩ := hrn | hdl\n⟨requires⟩ := ⟨ requires ⟨requires_clause⟩,* ⟩?\n⟨path⟩ := ⟨segments⟩ ⟨ ( ⟨refine_arg⟩,* ) …\n⟨qpath⟩ := &lt; ⟨ty⟩ as ⟨segments⟩&gt; :: …\n⟨reason⟩ := reason = ⟨literal⟩\n⟨refine_arg⟩ :=  @ ⟨ident⟩ |  # ⟨ident⟩ |  …\n⟨refine_param⟩ := ⟨mode⟩? ⟨ident⟩ ⟨ : …\n⟨refined_by⟩ := ⟨refine_param⟩,*\n⟨requires_clause⟩ := ⟨ forall ⟨refine_param⟩,+ . …\n⟨segment⟩ := ⟨ident⟩ ⟨ &lt; ⟨generic_arg⟩,* &gt; …\n⟨segments⟩ := ⟨segment⟩ ⟨:: ⟨segment⟩ ⟩*\n⟨sort⟩ :=  ⟨base_sort⟩ |  ( ⟨base_sort⟩,* ) -&gt; …\n⟨trailer_expr⟩ :=  ⟨epath⟩ . ⟨ident⟩ |  …\n⟨trait_assoc_reft⟩ := fn ⟨ident⟩ ( …\n⟨ty⟩ := _ | { ⟨ident⟩ ⟨,⟨ident⟩⟩* . …\n⟨variant⟩ := ⟨fields⟩ -&gt; ⟨variant_ret⟩ | …\n⟨variant_ret⟩ := ⟨path⟩ ⟨ [ ⟨refine_arg⟩,? ] …\nyes ⟨ , reason = ⟨literal⟩ ⟩? | no ⟨ , reason = …\nReturns true if the token at the requested position …\nParses a list of one ore more items separated by the …\nParses a list of zero or more items separated by a …\n⟨unary_expr⟩ := - ⟨unary_expr⟩ | ! …\nParses a list of zero or more items. Parsing continues …\n<code>&lt;qself as path&gt;::name</code>\nA <em>base</em> sort, e.g., <code>int</code> or <code>bool</code>.\nty\n<code>@n</code> or <code>#n</code>, the span corresponds to the span of the …\na bitvector sort, e.g., bitvec&lt;32&gt;\nexample <code>a: i32{a &gt; 0}</code>\nConstrained type: an exists without binder\nB{v: r}\nA <code>Path</code> but for refinement expressions\nA <em>function</em> sort of the form <code>(bi,...) -&gt; bo</code> where <code>bi..</code> and …\nThe <code>NodeId</code> is used to resolve the type to a corresponding …\n<code>B[r]</code>\nA sort that needs to be inferred.\nA literal token.\nA <code>NodeId</code> is a unique identifier we assign to some AST …\nA predicate that needs to hold\nA punctuated sequence of values of type <code>T</code> separated by …\nMutable or shared reference\nA <code>Path</code> but for sorts.\nA compressed span.\nA global function definition. It can be either an …\nexample <code>v: &amp;strg i32</code>\nA type with an optional binder, e.g, <code>i32</code>, <code>x: i32</code> or …\nA type constraint on a location\nThe sort arguments, i.e., the list <code>[int, bool]</code> in …\nBody of the function. If not present this definition …\nReturns true if either this <code>Punctuated</code> is empty, or it has …\nexample: <code>*x: i32{v. v = n+1}</code> or just <code>x &gt; 10</code>\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nReturns the argument unchanged.\nBinders are not allowed at this position, but we parse …\nexample: <code>i32&lt;@n&gt;</code>\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nCalls <code>U::from(self)</code>.\nDetermines whether this punctuated sequence is empty, …\nWhether the struct contains any path that needs to be …\nWhether the enum contains any path that needs to be …\nOptional list of universally quantified parameters\nAppends a syntax tree node onto the end of this punctuated …\nexample: <code>requires n &gt; 0</code>\nexample <code>i32{v:v &gt;= 0}</code>\nThe segments in the path\nsource span\nDetermines whether this punctuated sequence ends with a …")