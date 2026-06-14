import Squarefree.Lower.Step2Phi3
import Squarefree.Lower.DefectBt3

/-!
# §5 Step-2 BANDS: the third derivative `φ'''` as an EXPLICIT atom polynomial

`Step2Phi3` differentiates the Step-2/3 base phase `φ = phi X a ℓ₁ ℓ₂` once more, but keeps the
derivative `iteratedDeriv 3 φ` symbolic (it only proves it *exists*, via
`phi_iteratedDeriv2_hasDerivAt`).  The §5 Step-2 φ″-zero count needs the **closed form** of that
third derivative as an explicit polynomial in the `d̃`-tower and the `b̃`-tower.

* `phi3_poly` — `iteratedDeriv 3 φ` written as `K · Q / d̃⁸` with

  `Q = 6 d̃³ b̃' b̃'' + 2 d̃³ b̃ b̃''' + 180 d̃ (d̃')² b̃ b̃' + 90 d̃ d̃' d̃'' b̃²`
      `− 30 d̃² d̃' (b̃')² − 30 d̃² d̃' b̃ b̃'' − 30 d̃² d̃'' b̃ b̃' − 5 d̃² d̃''' b̃² − 210 (d̃')³ b̃²`,

  where `K = 12 ℓ₁ ℓ₂ (ℓ₂−ℓ₁) X a`, the `d̃`-tower is `d̃, d̃', d̃'', d̃'''` and the `b̃`-tower is
  `b̃, b̃' = deriv b̃, b̃'' = iteratedDeriv 2 b̃, b̃''' = iteratedDeriv 3 b̃`.

The proof differentiates the closed second derivative `φ'' = K·(…)/d̃⁶`.  Clearing the inner `/d̃`
collapses it to the single fraction `K·P/d̃⁷` (the private `g`), whose derivative is the clean
quotient `K·(P'·d̃ − 7 P d̃')/d̃⁸`; an `iteratedDeriv 2 φ =ᶠ g` then transfers the value.  The new
atom `b̃''' = iteratedDeriv 3 b̃` (`bt_iteratedDeriv3`) enters where `b̃'' ` is differentiated.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 4000000

/-- The reshaped closed second derivative `φ'' = K·P/d̃⁷` (a single fraction, the inner `/d̃` of the
`Step2Phi3.phi2` form having been cleared).  Differentiating this clean quotient is what produces
the explicit `φ'''` atom polynomial. -/
private noncomputable def g (X a ℓ₁ ℓ₂ s : ℝ) : ℝ :=
  (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a)
    * ( 2 * dtilde X s a ^ 2
          * ((deriv (fun u => dtilde X u a) (s + ℓ₁) - deriv (fun u => dtilde X u a) s) / ℓ₁) ^ 2
        + 2 * dtilde X s a ^ 2 * bt X a ℓ₁ s
          * ((iteratedDeriv 2 (fun u => dtilde X u a) (s + ℓ₁)
                - iteratedDeriv 2 (fun u => dtilde X u a) s) / ℓ₁)
        - 20 * dtilde X s a * deriv (fun u => dtilde X u a) s * bt X a ℓ₁ s
          * ((deriv (fun u => dtilde X u a) (s + ℓ₁) - deriv (fun u => dtilde X u a) s) / ℓ₁)
        - 5 * dtilde X s a * iteratedDeriv 2 (fun u => dtilde X u a) s * bt X a ℓ₁ s ^ 2
        + 30 * deriv (fun u => dtilde X u a) s ^ 2 * bt X a ℓ₁ s ^ 2 )
    / dtilde X s a ^ 7

/-- **`iteratedDeriv 3 φ` as an explicit polynomial in the `d̃`- and `b̃`-towers.**  This is the
gating closed form consumed by the §5 Step-2 φ″-zero count. -/
theorem phi3_poly {P : Globals} {a ℓ₁ ℓ₂ r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    iteratedDeriv 3 (fun u => phi P.X a ℓ₁ ℓ₂ u) r
      = (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a)
        * ( 6 * dtilde P.X r a ^ 3 * deriv (fun s => bt P.X a ℓ₁ s) r
                * iteratedDeriv 2 (fun s => bt P.X a ℓ₁ s) r
            + 2 * dtilde P.X r a ^ 3 * bt P.X a ℓ₁ r
                * iteratedDeriv 3 (fun s => bt P.X a ℓ₁ s) r
            + 180 * dtilde P.X r a * deriv (fun u => dtilde P.X u a) r ^ 2 * bt P.X a ℓ₁ r
                * deriv (fun s => bt P.X a ℓ₁ s) r
            + 90 * dtilde P.X r a * deriv (fun u => dtilde P.X u a) r
                * iteratedDeriv 2 (fun u => dtilde P.X u a) r * bt P.X a ℓ₁ r ^ 2
            - 30 * dtilde P.X r a ^ 2 * deriv (fun u => dtilde P.X u a) r
                * deriv (fun s => bt P.X a ℓ₁ s) r ^ 2
            - 30 * dtilde P.X r a ^ 2 * deriv (fun u => dtilde P.X u a) r * bt P.X a ℓ₁ r
                * iteratedDeriv 2 (fun s => bt P.X a ℓ₁ s) r
            - 30 * dtilde P.X r a ^ 2 * iteratedDeriv 2 (fun u => dtilde P.X u a) r * bt P.X a ℓ₁ r
                * deriv (fun s => bt P.X a ℓ₁ s) r
            - 5 * dtilde P.X r a ^ 2 * iteratedDeriv 3 (fun u => dtilde P.X u a) r * bt P.X a ℓ₁ r ^ 2
            - 210 * deriv (fun u => dtilde P.X u a) r ^ 3 * bt P.X a ℓ₁ r ^ 2 )
        / dtilde P.X r a ^ 8 := by
  -- `d̃`-tower atoms
  have hshift : HasDerivAt (fun s => s + ℓ₁) 1 r := (hasDerivAt_id r).add_const ℓ₁
  have hHD0 : HasDerivAt (fun s => dtilde P.X s a) (deriv (fun u => dtilde P.X u a) r) r := by
    have h := dtilde_r_hasDerivAt P.X_pos ha0 hr0; rw [h.deriv]; exact h
  have hHD1 : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) s)
      (iteratedDeriv 2 (fun u => dtilde P.X u a) r) r :=
    dtilde_deriv_hasDerivAt P.X_pos ha0 hr0
  have hHD2 : HasDerivAt (fun s => iteratedDeriv 2 (fun u => dtilde P.X u a) s)
      (iteratedDeriv 3 (fun u => dtilde P.X u a) r) r :=
    dtilde_iteratedDeriv2_hasDerivAt P.X_pos ha0 hr0
  have hHD1ℓ : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) (s + ℓ₁))
      (iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)) r := by
    have hbase := dtilde_deriv_hasDerivAt P.X_pos ha0 hrl
    have := hbase.comp r hshift; simpa using this
  have hHD2ℓ : HasDerivAt (fun s => iteratedDeriv 2 (fun u => dtilde P.X u a) (s + ℓ₁))
      (iteratedDeriv 3 (fun u => dtilde P.X u a) (r + ℓ₁)) r := by
    have hbase := dtilde_iteratedDeriv2_hasDerivAt P.X_pos ha0 hrl
    have := hbase.comp r hshift; simpa using this
  -- `b̃`-tower atoms (finite differences)
  have hbt : HasDerivAt (fun s => bt P.X a ℓ₁ s)
      ((deriv (fun s => dtilde P.X s a) (r + ℓ₁) - deriv (fun s => dtilde P.X s a) r) / ℓ₁) r :=
    bt_hasDerivAt P.X_pos ha0 hr0 hrl hℓne
  have hbp := (hHD1ℓ.sub hHD1).div_const ℓ₁
  have hbd := (hHD2ℓ.sub hHD2).div_const ℓ₁
  have hd0ne : dtilde P.X r a ≠ 0 := ne_of_gt (dtilde_pos P.X_pos ha0 hr0)
  -- clean pointwise powers (avoid `HasDerivAt.pow`'s Pi-level power)
  have hd2p : HasDerivAt (fun s => dtilde P.X s a ^ 2)
      (2 * dtilde P.X r a * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 2; simpa using this
  have hd1sq : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) s ^ 2)
      (2 * deriv (fun u => dtilde P.X u a) r * iteratedDeriv 2 (fun u => dtilde P.X u a) r) r := by
    have := hHD1.pow 2; simpa using this
  have hb2 : HasDerivAt (fun s => bt P.X a ℓ₁ s ^ 2)
      (2 * bt P.X a ℓ₁ r
        * ((deriv (fun s => dtilde P.X s a) (r + ℓ₁) - deriv (fun s => dtilde P.X s a) r) / ℓ₁)) r := by
    have := hbt.pow 2; simpa using this
  have hbp2 : HasDerivAt
      (fun s => ((deriv (fun u => dtilde P.X u a) (s + ℓ₁) - deriv (fun u => dtilde P.X u a) s) / ℓ₁) ^ 2)
      (2 * ((deriv (fun u => dtilde P.X u a) (r + ℓ₁) - deriv (fun u => dtilde P.X u a) r) / ℓ₁)
        * ((iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)
              - iteratedDeriv 2 (fun u => dtilde P.X u a) r) / ℓ₁)) r := by
    have := hbp.pow 2; simpa using this
  have hd7 : HasDerivAt (fun s => dtilde P.X s a ^ 7)
      (7 * dtilde P.X r a ^ 6 * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 7; simpa using this
  -- monomials of `P` and their sum
  have hM1 := (hd2p.const_mul 2).mul hbp2
  have hM2 := ((hd2p.const_mul 2).mul hbt).mul hbd
  have hM3 := (((hHD0.const_mul 20).mul hHD1).mul hbt).mul hbp
  have hM4 := ((hHD0.const_mul 5).mul hHD2).mul hb2
  have hM5 := (hd1sq.const_mul 30).mul hb2
  have hP := (((hM1.add hM2).sub hM3).sub hM4).add hM5
  -- `iteratedDeriv 2 φ =ᶠ g` near `r`
  have hee : iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) =ᶠ[nhds r] (fun s => g P.X a ℓ₁ ℓ₂ s) := by
    have hU : {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} ∈ nhds r := by
      have hopen : IsOpen {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} := by
        have h1 : IsOpen {s : ℝ | 0 < s} := isOpen_lt continuous_const continuous_id
        have h2 : IsOpen {s : ℝ | 0 < s + ℓ₁} :=
          isOpen_lt continuous_const (continuous_id.add continuous_const)
        simpa [Set.setOf_and] using h1.inter h2
      exact hopen.mem_nhds ⟨hr0, hrl⟩
    refine Filter.eventuallyEq_of_mem hU ?_
    intro s hs
    show iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) s = g P.X a ℓ₁ ℓ₂ s
    rw [phi_iteratedDeriv2_eq ha0 hs.1 hs.2 hℓne]
    have hds : dtilde P.X s a ≠ 0 := ne_of_gt (dtilde_pos P.X_pos ha0 hs.1)
    simp only [g]
    field_simp
    ring
  -- `HasDerivAt g (explicit value) r`
  have hgd : HasDerivAt (fun s => g P.X a ℓ₁ ℓ₂ s)
      ((12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a)
        * ( 6 * dtilde P.X r a ^ 3 * deriv (fun s => bt P.X a ℓ₁ s) r
                * iteratedDeriv 2 (fun s => bt P.X a ℓ₁ s) r
            + 2 * dtilde P.X r a ^ 3 * bt P.X a ℓ₁ r
                * iteratedDeriv 3 (fun s => bt P.X a ℓ₁ s) r
            + 180 * dtilde P.X r a * deriv (fun u => dtilde P.X u a) r ^ 2 * bt P.X a ℓ₁ r
                * deriv (fun s => bt P.X a ℓ₁ s) r
            + 90 * dtilde P.X r a * deriv (fun u => dtilde P.X u a) r
                * iteratedDeriv 2 (fun u => dtilde P.X u a) r * bt P.X a ℓ₁ r ^ 2
            - 30 * dtilde P.X r a ^ 2 * deriv (fun u => dtilde P.X u a) r
                * deriv (fun s => bt P.X a ℓ₁ s) r ^ 2
            - 30 * dtilde P.X r a ^ 2 * deriv (fun u => dtilde P.X u a) r * bt P.X a ℓ₁ r
                * iteratedDeriv 2 (fun s => bt P.X a ℓ₁ s) r
            - 30 * dtilde P.X r a ^ 2 * iteratedDeriv 2 (fun u => dtilde P.X u a) r * bt P.X a ℓ₁ r
                * deriv (fun s => bt P.X a ℓ₁ s) r
            - 5 * dtilde P.X r a ^ 2 * iteratedDeriv 3 (fun u => dtilde P.X u a) r * bt P.X a ℓ₁ r ^ 2
            - 210 * deriv (fun u => dtilde P.X u a) r ^ 3 * bt P.X a ℓ₁ r ^ 2 )
        / dtilde P.X r a ^ 8) r := by
    rw [(bt_hasDerivAt P.X_pos ha0 hr0 hrl hℓne).deriv,
        bt_iteratedDeriv2 P.X_pos ha0 hr0 hrl hℓne,
        bt_iteratedDeriv3 P.X_pos ha0 hr0 hrl hℓne]
    have hquot := (hP.const_mul (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a)).div hd7
      (pow_ne_zero 7 hd0ne)
    simp only [g]
    convert hquot using 1
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
    field_simp
    ring
  rw [iteratedDeriv_succ, hee.deriv_eq]
  exact hgd.deriv

end Squarefree
