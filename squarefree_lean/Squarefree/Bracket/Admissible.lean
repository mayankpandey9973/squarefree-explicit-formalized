import Squarefree.Params
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib

/-!
# §7 admissibility envelope (`AdmissibleW`)

Faithful statement of the §7 full admissibility envelope from `../explicit_writeup.md`
(lines 1437–1467). This is a plain `structure` (it carries the real constant field `c`),
not a `Prop`. See `CLAUDE.md` §3.
-/

open Classical Finset

namespace Squarefree

/-- §7 full admissibility envelope (writeup 1437–1467): the 21 root-form entries (k-th roots
of the proof's `Wᵏ≪…` constraints) under one absolute constant `c`, plus the scale-level
§4.3 side conditions `R>1`, `T₁>1`. (The proof-internal side conditions `0<δ₁(h)<1`, `|F''|≍1`
are established inside the Prop 7.1 proof, not here.) -/
structure AdmissibleW (P : Globals) (S : Scale P) (W : ℝ) where
  W_pos : 0 < W
  c : ℝ
  c_pos : 0 < c
  e01 : W ≤ c * (P.H ^ (1/16:ℝ) * S.x ^ (5/16:ℝ) * S.Ω ^ (1/4:ℝ))
  e02 : W ≤ c * (P.H ^ (1/28:ℝ) * S.x ^ (5/28:ℝ) * P.G ^ (1/14:ℝ) * S.Ω ^ (1/2:ℝ))
  e03 : W ≤ c * (P.H ^ (1/40:ℝ) * S.x ^ (1/8:ℝ) * P.G ^ (1/5:ℝ) * S.Ω ^ (3/5:ℝ))
  e04 : W ≤ c * (P.H ^ (1/18:ℝ) * S.x ^ (1/18:ℝ) * P.G ^ (-1/3:ℝ) * S.Ω ^ (-7/9:ℝ))
  e05 : W ≤ c * (P.H ^ (1/42:ℝ) * S.x ^ (1/42:ℝ) * P.G ^ (-1/21:ℝ) * S.Ω ^ (1/7:ℝ))
  e06 : W ≤ c * (P.H ^ (1/30:ℝ) * S.x ^ (1/30:ℝ) * S.Ω ^ (-2/15:ℝ))
  e07 : W ≤ c * (P.H ^ (1/54:ℝ) * S.x ^ (1/54:ℝ) * P.G ^ (2/27:ℝ) * S.Ω ^ (8/27:ℝ))
  e08 : W ≤ c * (P.H ^ (1/30:ℝ) * S.x ^ (1/6:ℝ) * P.G ^ (4/15:ℝ) * S.Ω ^ (4/5:ℝ))
  e09 : W ≤ c * (P.H ^ (1/42:ℝ) * S.x ^ (5/42:ℝ) * P.G ^ (5/21:ℝ) * S.Ω ^ (17/21:ℝ))
  e10 : W ≤ c * (P.H ^ (1/48:ℝ) * S.x ^ (5/48:ℝ) * P.G ^ (1/8:ℝ) * S.Ω ^ (7/24:ℝ))
  e11 : W ≤ c * (P.H ^ (1/16:ℝ) * S.x ^ (1/16:ℝ) * P.G ^ (-1/16:ℝ) * S.Ω ^ (1/16:ℝ))
  e12 : W ≤ c * (P.H ^ (1/22:ℝ) * S.x ^ (1/22:ℝ) * P.G ^ (1/11:ℝ) * S.Ω ^ (3/11:ℝ))
  e13 : W ≤ c * (P.H ^ (1/16:ℝ) * S.x ^ (1/16:ℝ) * P.G ^ (1/8:ℝ) * S.Ω ^ (3/8:ℝ))
  e14 : W ≤ c * (P.H ^ (1/84:ℝ) * S.x ^ (5/84:ℝ) * P.G ^ (1/7:ℝ) * S.Ω ^ (11/21:ℝ))
  e15 : W ≤ c * (P.H ^ (1/28:ℝ) * S.x ^ (1/28:ℝ) * P.G ^ (1/28:ℝ) * S.Ω ^ (11/28:ℝ))
  e16 : W ≤ c * (P.H ^ (1/34:ℝ) * S.x ^ (1/34:ℝ) * P.G ^ (2/17:ℝ) * S.Ω ^ (8/17:ℝ))
  e17 : W ≤ c * (P.H ^ (1/28:ℝ) * S.x ^ (1/28:ℝ) * P.G ^ (1/7:ℝ) * S.Ω ^ (4/7:ℝ))
  e18 : W ≤ c * (P.H ^ (1/16:ℝ) * S.x ^ (-1/16:ℝ))
  e19 : W ≤ c * (P.H ^ (1/28:ℝ) * S.x ^ (-1/28:ℝ) * P.G ^ (1/14:ℝ) * S.Ω ^ (5/14:ℝ))
  e20 : W ≤ c * (P.H ^ (1/24:ℝ) * S.x ^ (5/24:ℝ) * P.G ^ (1/4:ℝ) * S.Ω ^ (7/12:ℝ))
  e21 : W ≤ c * (P.H ^ (1/36:ℝ) * S.x ^ (5/36:ℝ) * P.G ^ (2/9:ℝ) * S.Ω ^ (2/3:ℝ))
  R_gt_one : 1 < S.R
  T1_gt_one : 1 < S.T₁

end Squarefree
