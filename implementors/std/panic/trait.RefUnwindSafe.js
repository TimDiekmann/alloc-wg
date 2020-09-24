(function() {var implementors = {};
implementors["alloc_wg"] = [{"text":"impl&lt;T:&nbsp;?Sized, A&gt; RefUnwindSafe for Box&lt;T, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;K, V, A&gt; RefUnwindSafe for BTreeMap&lt;K, V, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; RefUnwindSafe for Iter&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; RefUnwindSafe for IterMut&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;K, V, A&gt; RefUnwindSafe for IntoIter&lt;K, V, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; RefUnwindSafe for Keys&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; RefUnwindSafe for Values&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; RefUnwindSafe for ValuesMut&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;K, V, A&gt; RefUnwindSafe for IntoKeys&lt;K, V, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;K, V, A&gt; RefUnwindSafe for IntoValues&lt;K, V, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; RefUnwindSafe for Range&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V&gt; RefUnwindSafe for RangeMut&lt;'a, K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V, A&gt; RefUnwindSafe for VacantEntry&lt;'a, K, V, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V, A&gt; RefUnwindSafe for OccupiedEntry&lt;'a, K, V, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V, F, A&gt; RefUnwindSafe for DrainFilter&lt;'a, K, V, F, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;F: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, K, V, A&gt; RefUnwindSafe for Entry&lt;'a, K, V, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;K: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;T, A&gt; RefUnwindSafe for BTreeSet&lt;T, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T&gt; RefUnwindSafe for Iter&lt;'a, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;T, A&gt; RefUnwindSafe for IntoIter&lt;T, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T&gt; RefUnwindSafe for Range&lt;'a, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T, A&gt; RefUnwindSafe for Difference&lt;'a, T, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T&gt; RefUnwindSafe for SymmetricDifference&lt;'a, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T, A&gt; RefUnwindSafe for Intersection&lt;'a, T, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T&gt; RefUnwindSafe for Union&lt;'a, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T, F, A&gt; RefUnwindSafe for DrainFilter&lt;'a, T, F, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;F: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl RefUnwindSafe for TryReserveError","synthetic":true,"types":[]},{"text":"impl&lt;A&gt; RefUnwindSafe for String&lt;A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;A&gt; RefUnwindSafe for FromUtf8Error&lt;A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl RefUnwindSafe for FromUtf16Error","synthetic":true,"types":[]},{"text":"impl&lt;'a, A&gt; RefUnwindSafe for Drain&lt;'a, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;T, A&gt; RefUnwindSafe for Vec&lt;T, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;T, A&gt; RefUnwindSafe for IntoIter&lt;T, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T, A&gt; RefUnwindSafe for Drain&lt;'a, T, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, I, A&gt; RefUnwindSafe for Splice&lt;'a, I, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;I: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;&lt;I as Iterator&gt;::Item: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]},{"text":"impl&lt;'a, T, F, A&gt; RefUnwindSafe for DrainFilter&lt;'a, T, F, A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;F: RefUnwindSafe,<br>&nbsp;&nbsp;&nbsp;&nbsp;T: RefUnwindSafe,&nbsp;</span>","synthetic":true,"types":[]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()