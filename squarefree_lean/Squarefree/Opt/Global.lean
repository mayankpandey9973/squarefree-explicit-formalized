import Squarefree.Opt.Strip

/-!
# §9 global assembly

The §9 optimization (`18977g+15315u<2`, the `W_old/W_{≠0}` comparison) now lives *inside*
`dblock_bound`'s on-strip case (`Opt/Strip.lean`), so there is no separate `section9` lemma.
The remaining §9/§1 assembly — combining `a_decomposition` (§3), `dblock_bound`/`dblock_small_omega`
(§8/§9, here), and `prop_2_4` (§2) over the `O(log X)=X^{O(u)}` dyadic Ω-scales — is carried out
in `key_dyadic_estimate` (`Main.lean`), together with a dyadic-partition plumbing lemma added when
that proof is written.

(The old `section9_DBlock_le` stub was restated as `dblock_bound` in `Opt/Strip.lean`.)
-/

namespace Squarefree

end Squarefree
