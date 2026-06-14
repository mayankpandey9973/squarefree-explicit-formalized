import Squarefree.Lower.DefectBt
import Squarefree.Lower.DefectDeriv5
import Squarefree.Lower.Step2CurvCurv2

/-!
# §5 derivative calculus: the 3rd derivative of `b̃ₐ` + its finite-difference error

`b̃ₐ` (`bt`, `DefectBt`) is the first finite difference `(d̃ₐ(·+ℓ) − d̃ₐ)/ℓ` used as the actual
(non-smooth) atom in the §5 Step-2 phase.  `DefectBt` already computes `b̃ₐ' , b̃ₐ''` as the
corresponding finite differences of `d̃ₐ' , d̃ₐ''`.  This file extends the tower by one order:

* `bt_iteratedDeriv3` — `b̃ₐ'''(r) = (d̃ₐ'''(r+ℓ) − d̃ₐ'''(r))/ℓ` (the finite difference of `d̃ₐ'''`),
  mirroring `bt_iteratedDeriv2`;
* `bt_iteratedDeriv3_fd_error` — the **tight finite-difference correction**
  `|b̃ₐ'''(r) − d̃ₐ''''(r)| ≤ ℓ₁·sup|d̃ₐ⁽⁵⁾|`, via the double mean-value bound `fd_error_bound`
  fed by `dtilde_iteratedDeriv4_hasDerivAt` and the new fifth-derivative scale bound
  `dtilde_d5_upper`.  This is the gating prerequisite for the §5 Step-2 φ″-zero count (`χ'''`
  finite-difference correction).
-/

namespace Squarefree

open Real

/-- **The third derivative of `b̃ₐ` is the finite difference of `d̃ₐ'''`.**  Mirrors
`bt_iteratedDeriv2`, one order up. -/
theorem bt_iteratedDeriv3 {X a ℓ r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r)
    (hrl : 0 < r + ℓ) (hℓ : ℓ ≠ 0) :
    iteratedDeriv 3 (fun s => bt X a ℓ s) r
      = (iteratedDeriv 3 (fun s => dtilde X s a) (r + ℓ)
          - iteratedDeriv 3 (fun s => dtilde X s a) r) / ℓ := by
  rw [iteratedDeriv_succ]
  -- on the open window `{s | 0 < s ∧ 0 < s + ℓ}`, `b̃ₐ''` is the finite difference of `d̃ₐ''`.
  have hU : {s : ℝ | 0 < s ∧ 0 < s + ℓ} ∈ nhds r := by
    have hopen : IsOpen {s : ℝ | 0 < s ∧ 0 < s + ℓ} := by
      have h1 : IsOpen {s : ℝ | 0 < s} := isOpen_lt continuous_const continuous_id
      have h2 : IsOpen {s : ℝ | 0 < s + ℓ} :=
        isOpen_lt continuous_const (continuous_id.add continuous_const)
      simpa [Set.setOf_and] using h1.inter h2
    exact hopen.mem_nhds ⟨hr, hrl⟩
  have hee : iteratedDeriv 2 (fun s => bt X a ℓ s)
      =ᶠ[nhds r] (fun s => (iteratedDeriv 2 (fun t => dtilde X t a) (s + ℓ)
          - iteratedDeriv 2 (fun t => dtilde X t a) s) / ℓ) := by
    refine Filter.eventuallyEq_of_mem hU ?_
    intro s hs
    exact bt_iteratedDeriv2 hX ha hs.1 hs.2 hℓ
  rw [hee.deriv_eq]
  -- differentiate the finite difference of `d̃ₐ''`.
  have hshift : HasDerivAt (fun s => iteratedDeriv 2 (fun t => dtilde X t a) (s + ℓ))
      (iteratedDeriv 3 (fun u => dtilde X u a) (r + ℓ)) r := by
    have hadd : HasDerivAt (fun s => s + ℓ) 1 r := (hasDerivAt_id r).add_const ℓ
    have := (dtilde_iteratedDeriv2_hasDerivAt hX ha hrl).comp r hadd
    simpa using this
  have hbase : HasDerivAt (fun s => iteratedDeriv 2 (fun t => dtilde X t a) s)
      (iteratedDeriv 3 (fun u => dtilde X u a) r) r :=
    dtilde_iteratedDeriv2_hasDerivAt hX ha hr
  exact ((hshift.sub hbase).div_const ℓ).deriv

/-- **Tight finite-difference correction for `b̃ₐ'''`.**  On the §5 band window
`[r, r+ℓ₁] ⊆ [(1/72)R, 16R]`, the first finite difference of `d̃ₐ'''` differs from `d̃ₐ''''(r)` by
at most `ℓ₁·sup|d̃ₐ⁽⁵⁾| ≤ ℓ₁·(1.18098·10³²·D/R⁵)`.  This is the order-up analogue of the `ε₃`
bound (`he3`) in `phif_curvature_lower_curv`, feeding the §5 Step-2 `χ'''` correction. -/
theorem bt_iteratedDeriv3_fd_error {P : Globals} {S : Scale P} {a ℓ₁ r : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A) (hℓ1 : 0 < ℓ₁)
    (hwin : ∀ x ∈ Set.Icc r (r + ℓ₁), (1 / 72) * S.R ≤ x ∧ x ≤ 16 * S.R ∧ 0 < x) :
    |(iteratedDeriv 3 (fun u => dtilde P.X u a) (r + ℓ₁)
        - iteratedDeriv 3 (fun u => dtilde P.X u a) r) / ℓ₁
      - iteratedDeriv 4 (fun u => dtilde P.X u a) r|
      ≤ ℓ₁ * (118098000000000000000000000000000 * (S.D / S.R ^ 5)) :=
  fd_error_bound (f := fun t => iteratedDeriv 3 (fun u => dtilde P.X u a) t)
    (g := fun t => iteratedDeriv 4 (fun u => dtilde P.X u a) t)
    (h := fun t => iteratedDeriv 5 (fun u => dtilde P.X u a) t)
    (M := 118098000000000000000000000000000 * (S.D / S.R ^ 5)) hℓ1
    (fun x hx => dtilde_iteratedDeriv3_hasDerivAt P.X_pos ha0 (hwin x hx).2.2)
    (fun x hx => dtilde_iteratedDeriv4_hasDerivAt P.X_pos ha0 (hwin x hx).2.2)
    (fun x hx => by
      obtain ⟨hxl, hxr, hxpos⟩ := hwin x hx
      exact dtilde_d5_upper hAD ha0 hxpos ha_lo ha_hi hxl hxr)

end Squarefree
