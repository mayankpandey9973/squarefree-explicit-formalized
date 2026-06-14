import Squarefree.Lower.Step2Curvature2

/-!
# §5 Step-2 BANDS: the third derivative `φ_f'''` — differentiation infrastructure

This file extends the second-derivative tower of `Step2Curvature2` by one order, building the
**third derivative** of the Step-2/3 phase `φ_f` (needed by the §5 Step-2 φ″-zero count, which
differentiates the ratio `χ''/ψ''`).

* `phi_iteratedDeriv2_hasDerivAt` — `s ↦ iteratedDeriv 2 phi s` is differentiable, with derivative
  `iteratedDeriv 3 phi`.  (Differentiate the closed second derivative `φ'' = K·(…)/d̃⁶`.)
* `phif_iteratedDeriv3_eq` — the **explicit** product-rule value of `φ_f'''`, keeping the atoms
  `d̃, d̃', d̃'', d̃'''` and `φ, φ', φ'', φ'''` symbolic (exactly as `phif_iteratedDeriv2_eq` keeps
  `φ''` symbolic).  With `ψ = d̃⁴/(6Xa)`:

  `φ_f''' = ψ'''·(f+φ) + 3ψ''·φ' + 3ψ'·φ'' + ψ·φ'''`,

  where `ψ''' = (24 d̃(d̃')³ + 36 d̃² d̃' d̃'' + 4 d̃³ d̃''')/(6Xa)`,
  `ψ'' = (12 d̃²(d̃')² + 4 d̃³ d̃'')/(6Xa)`, `ψ' = 4 d̃³ d̃'/(6Xa)`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- The closed-form second derivative of `φ = phi X a ℓ₁ ℓ₂`, as a function of `s`
(matching `phi_iteratedDeriv2_eq`). -/
private noncomputable def phi2 (X a ℓ₁ ℓ₂ s : ℝ) : ℝ :=
  (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a)
    * ( ((deriv (fun u => dtilde X u a) (s + ℓ₁)
            - deriv (fun u => dtilde X u a) s) / ℓ₁)
          * (2 * ((deriv (fun u => dtilde X u a) (s + ℓ₁)
                - deriv (fun u => dtilde X u a) s) / ℓ₁) * dtilde X s a
              - 5 * bt X a ℓ₁ s * deriv (fun u => dtilde X u a) s)
        + bt X a ℓ₁ s
          * (2 * ((iteratedDeriv 2 (fun u => dtilde X u a) (s + ℓ₁)
                - iteratedDeriv 2 (fun u => dtilde X u a) s) / ℓ₁) * dtilde X s a
              - 3 * ((deriv (fun u => dtilde X u a) (s + ℓ₁)
                - deriv (fun u => dtilde X u a) s) / ℓ₁) * deriv (fun u => dtilde X u a) s
              - 5 * bt X a ℓ₁ s * iteratedDeriv 2 (fun u => dtilde X u a) s)
        - 6 * bt X a ℓ₁ s
            * (2 * ((deriv (fun u => dtilde X u a) (s + ℓ₁)
                  - deriv (fun u => dtilde X u a) s) / ℓ₁) * dtilde X s a
              - 5 * bt X a ℓ₁ s * deriv (fun u => dtilde X u a) s)
            * deriv (fun u => dtilde X u a) s / dtilde X s a )
    / (dtilde X s a) ^ 6

/-- `iteratedDeriv 2 phi =ᶠ phi2` near `r > 0` (with `r + ℓ₁ > 0`). -/
private theorem phi_iteratedDeriv2_eventuallyEq {P : Globals} {a ℓ₁ ℓ₂ r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) =ᶠ[nhds r] (fun s => phi2 P.X a ℓ₁ ℓ₂ s) := by
  have hU : {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} ∈ nhds r := by
    have hopen : IsOpen {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} := by
      have h1 : IsOpen {s : ℝ | 0 < s} := isOpen_lt continuous_const continuous_id
      have h2 : IsOpen {s : ℝ | 0 < s + ℓ₁} :=
        isOpen_lt continuous_const (continuous_id.add continuous_const)
      simpa [Set.setOf_and] using h1.inter h2
    exact hopen.mem_nhds ⟨hr0, hrl⟩
  refine Filter.eventuallyEq_of_mem hU ?_
  intro s hs
  show iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) s = phi2 P.X a ℓ₁ ℓ₂ s
  rw [phi_iteratedDeriv2_eq ha0 hs.1 hs.2 hℓne]
  simp only [phi2]

/-- `phi2` is differentiable at `r > 0` (with `r + ℓ₁ > 0`).  Its derivative (kept symbolic in the
`d̃`-tower through `deriv`/`iteratedDeriv`) is the value used as `φ'''`.  Mirrors `phi1_hasDerivAt`,
one order up; the new highest atom is `d̃''' = iteratedDeriv 3 d̃` (from
`dtilde_iteratedDeriv2_hasDerivAt`). -/
private theorem phi2_hasDerivAt {P : Globals} {a ℓ₁ ℓ₂ r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    HasDerivAt (fun s => phi2 P.X a ℓ₁ ℓ₂ s) (deriv (fun s => phi2 P.X a ℓ₁ ℓ₂ s) r) r := by
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
  have hbt : HasDerivAt (fun s => bt P.X a ℓ₁ s)
      ((deriv (fun u => dtilde P.X u a) (r + ℓ₁) - deriv (fun u => dtilde P.X u a) r) / ℓ₁) r :=
    bt_hasDerivAt P.X_pos ha0 hr0 hrl hℓne
  have hbp := (hHD1ℓ.sub hHD1).div_const ℓ₁
  have hbd := (hHD2ℓ.sub hHD2).div_const ℓ₁
  have hd0ne : dtilde P.X r a ≠ 0 := ne_of_gt (dtilde_pos P.X_pos ha0 hr0)
  have hd6 : HasDerivAt (fun s => (dtilde P.X s a) ^ 6)
      (6 * (dtilde P.X r a) ^ 5 * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 6; simpa using this
  have hd6ne : (dtilde P.X r a) ^ 6 ≠ 0 := pow_ne_zero 6 hd0ne
  -- bracket1(s) = 2·b̃'(s)·d̃(s) − 5·b̃(s)·d̃'(s)
  have hbracket1 := ((hbp.const_mul 2).mul hHD0).sub ((hbt.const_mul 5).mul hHD1)
  -- inner2(s) = 2·b̃''(s)·d̃(s) − 3·b̃'(s)·d̃'(s) − 5·b̃(s)·d̃''(s)
  have hinner2 := (((hbd.const_mul 2).mul hHD0).sub ((hbp.const_mul 3).mul hHD1)).sub
    ((hbt.const_mul 5).mul hHD2)
  have hterm1 := hbp.mul hbracket1
  have hterm2 := hbt.mul hinner2
  have hterm3 := (((hbt.const_mul 6).mul hbracket1).mul hHD1).div hHD0 hd0ne
  have hnum0 := (hterm1.add hterm2).sub hterm3
  have hKnum := hnum0.const_mul (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a)
  have hquot := hKnum.div hd6 hd6ne
  have hphi2_eq : (fun s => phi2 P.X a ℓ₁ ℓ₂ s)
      = (fun s => (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a)
          * ( ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                  - deriv (fun u => dtilde P.X u a) s) / ℓ₁)
                * (2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                      - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
                    - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s)
              + bt P.X a ℓ₁ s
                * (2 * ((iteratedDeriv 2 (fun u => dtilde P.X u a) (s + ℓ₁)
                      - iteratedDeriv 2 (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
                    - 3 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                      - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * deriv (fun u => dtilde P.X u a) s
                    - 5 * bt P.X a ℓ₁ s * iteratedDeriv 2 (fun u => dtilde P.X u a) s)
              - 6 * bt P.X a ℓ₁ s
                  * (2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                        - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
                    - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s)
                  * deriv (fun u => dtilde P.X u a) s / dtilde P.X s a )
          / (dtilde P.X s a) ^ 6) := by
    funext s; rw [phi2]
  rw [hphi2_eq]
  exact hquot.differentiableAt.hasDerivAt

/-- **`iteratedDeriv 2 phi` is differentiable, with derivative `iteratedDeriv 3 phi`** (`φ = phi …`).
This is the §5 Step-2 third derivative of the smooth-bracket phase, kept symbolic in the `d̃`-tower. -/
theorem phi_iteratedDeriv2_hasDerivAt {P : Globals} {a ℓ₁ ℓ₂ r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    HasDerivAt (fun s => iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      (iteratedDeriv 3 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r := by
  have hee := phi_iteratedDeriv2_eventuallyEq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    ha0 hr0 hrl hℓne
  have hid3 : iteratedDeriv 3 (fun u => phi P.X a ℓ₁ ℓ₂ u) r
      = deriv (fun s => phi2 P.X a ℓ₁ ℓ₂ s) r := by
    rw [iteratedDeriv_succ]; exact hee.deriv_eq
  rw [hid3]
  exact (phi2_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne).congr_of_eventuallyEq
    hee

/-- The closed-form second derivative of `φ_f = phif X a ℓ₁ ℓ₂ f`, as a function of `s`
(matching `phif_iteratedDeriv2_eq`):
`φ_f''(s) = (12 d̃²(d̃')² + 4 d̃³ d̃'')/(6Xa)·(f+φ) + (8 d̃³ d̃')/(6Xa)·φ' + d̃⁴/(6Xa)·φ''`. -/
private noncomputable def phif2 (X a ℓ₁ ℓ₂ f s : ℝ) : ℝ :=
  (12 * (dtilde X s a) ^ 2 * (deriv (fun u => dtilde X u a) s) ^ 2
        + 4 * (dtilde X s a) ^ 3 * iteratedDeriv 2 (fun u => dtilde X u a) s)
      / (6 * X * a) * (f + phi X a ℓ₁ ℓ₂ s)
    + (8 * (dtilde X s a) ^ 3 * deriv (fun u => dtilde X u a) s) / (6 * X * a)
      * deriv (fun u => phi X a ℓ₁ ℓ₂ u) s
    + (dtilde X s a) ^ 4 / (6 * X * a)
      * iteratedDeriv 2 (fun u => phi X a ℓ₁ ℓ₂ u) s

/-- `iteratedDeriv 2 φ_f =ᶠ phif2` near `r > 0` (with `r + ℓ₁ > 0`). -/
private theorem phif_iteratedDeriv2_eventuallyEq {P : Globals} {a ℓ₁ ℓ₂ f r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) =ᶠ[nhds r]
      (fun s => phif2 P.X a ℓ₁ ℓ₂ f s) := by
  have hU : {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} ∈ nhds r := by
    have hopen : IsOpen {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} := by
      have h1 : IsOpen {s : ℝ | 0 < s} := isOpen_lt continuous_const continuous_id
      have h2 : IsOpen {s : ℝ | 0 < s + ℓ₁} :=
        isOpen_lt continuous_const (continuous_id.add continuous_const)
      simpa [Set.setOf_and] using h1.inter h2
    exact hopen.mem_nhds ⟨hr0, hrl⟩
  refine Filter.eventuallyEq_of_mem hU ?_
  intro s hs
  show iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) s = phif2 P.X a ℓ₁ ℓ₂ f s
  rw [phif_iteratedDeriv2_eq ha0 hs.1 hs.2 hℓne]
  simp only [phif2]

/-- **The explicit product-rule value of `φ_f'''`.**  With `ψ = d̃⁴/(6Xa)`,
`φ_f''' = ψ'''·(f+φ) + 3ψ''·φ' + 3ψ'·φ'' + ψ·φ'''`, expanded into atoms:

  `φ_f''' = (24 d̃(d̃')³ + 36 d̃² d̃' d̃'' + 4 d̃³ d̃''')/(6Xa)·(f+φ)`
         `+ (36 d̃²(d̃')² + 12 d̃³ d̃'')/(6Xa)·φ'`
         `+ (12 d̃³ d̃')/(6Xa)·φ''`
         `+ d̃⁴/(6Xa)·φ'''`,

keeping `φ, φ', φ'', φ'''` (of `phi`) and the `d̃`-tower symbolic.  Differentiate
`phif_iteratedDeriv2_eq` via the product rule; the new atoms `d̃''' = iteratedDeriv 3 d̃` and
`φ''' = iteratedDeriv 3 phi` come from `dtilde_iteratedDeriv2_hasDerivAt` and
`phi_iteratedDeriv2_hasDerivAt`. -/
theorem phif_iteratedDeriv3_eq {P : Globals} {a ℓ₁ ℓ₂ f r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    iteratedDeriv 3 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r
      = (24 * dtilde P.X r a * (deriv (fun u => dtilde P.X u a) r) ^ 3
            + 36 * (dtilde P.X r a) ^ 2 * deriv (fun u => dtilde P.X u a) r
                * iteratedDeriv 2 (fun u => dtilde P.X u a) r
            + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 3 (fun u => dtilde P.X u a) r)
          / (6 * P.X * a) * (f + phi P.X a ℓ₁ ℓ₂ r)
        + (36 * (dtilde P.X r a) ^ 2 * (deriv (fun u => dtilde P.X u a) r) ^ 2
            + 12 * (dtilde P.X r a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) r)
          / (6 * P.X * a) * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r
        + (12 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) / (6 * P.X * a)
          * iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r
        + (dtilde P.X r a) ^ 4 / (6 * P.X * a)
          * iteratedDeriv 3 (fun u => phi P.X a ℓ₁ ℓ₂ u) r := by
  have hee := phif_iteratedDeriv2_eventuallyEq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    ha0 hr0 hrl hℓne
  have hid3 : iteratedDeriv 3 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r
      = deriv (fun s => phif2 P.X a ℓ₁ ℓ₂ f s) r := by
    rw [iteratedDeriv_succ]; exact hee.deriv_eq
  rw [hid3]
  -- atoms
  have hHD0 : HasDerivAt (fun s => dtilde P.X s a) (deriv (fun u => dtilde P.X u a) r) r := by
    have h := dtilde_r_hasDerivAt P.X_pos ha0 hr0; rw [h.deriv]; exact h
  have hHD1 : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) s)
      (iteratedDeriv 2 (fun u => dtilde P.X u a) r) r :=
    dtilde_deriv_hasDerivAt P.X_pos ha0 hr0
  have hHD2 : HasDerivAt (fun s => iteratedDeriv 2 (fun u => dtilde P.X u a) s)
      (iteratedDeriv 3 (fun u => dtilde P.X u a) r) r :=
    dtilde_iteratedDeriv2_hasDerivAt P.X_pos ha0 hr0
  have hphi : HasDerivAt (fun s => phi P.X a ℓ₁ ℓ₂ s)
      (deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    (phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl
      hℓne).differentiableAt.hasDerivAt
  have hphi' : HasDerivAt (fun s => deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      (iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    phi_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  have hphi'' : HasDerivAt (fun s => iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      (iteratedDeriv 3 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    phi_iteratedDeriv2_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  -- clean pointwise power sub-terms (avoid `HasDerivAt.pow`'s Pi-level power)
  have hd2 : HasDerivAt (fun s => (dtilde P.X s a) ^ 2)
      (2 * dtilde P.X r a * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 2; simpa using this
  have hd3 : HasDerivAt (fun s => (dtilde P.X s a) ^ 3)
      (3 * (dtilde P.X r a) ^ 2 * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 3; simpa using this
  have hd4 : HasDerivAt (fun s => (dtilde P.X s a) ^ 4)
      (4 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 4; simpa using this
  have hd1sq : HasDerivAt (fun s => (deriv (fun u => dtilde P.X u a) s) ^ 2)
      (2 * deriv (fun u => dtilde P.X u a) r * iteratedDeriv 2 (fun u => dtilde P.X u a) r) r := by
    have := hHD1.pow 2; simpa using this
  -- piece A: A0(s)·(f+φ), A0 = (12 d̃²(d̃')² + 4 d̃³ d̃'')/(6Xa)
  have hAnum : HasDerivAt (fun s => 12 * (dtilde P.X s a) ^ 2 * (deriv (fun u => dtilde P.X u a) s) ^ 2
        + 4 * (dtilde P.X s a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) s)
      (24 * dtilde P.X r a * (deriv (fun u => dtilde P.X u a) r) ^ 3
        + 36 * (dtilde P.X r a) ^ 2 * deriv (fun u => dtilde P.X u a) r
            * iteratedDeriv 2 (fun u => dtilde P.X u a) r
        + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 3 (fun u => dtilde P.X u a) r) r := by
    have h := ((hd2.const_mul 12).mul hd1sq).add ((hd3.const_mul 4).mul hHD2)
    convert h using 1; ring
  have hA0 := hAnum.div_const (6 * P.X * a)
  have hfphi : HasDerivAt (fun s => f + phi P.X a ℓ₁ ℓ₂ s)
      (deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r := hphi.const_add f
  have hpieceA := hA0.mul hfphi
  -- piece B: B0(s)·φ', B0 = (8 d̃³ d̃')/(6Xa)
  have hBnum : HasDerivAt (fun s => 8 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s)
      (24 * (dtilde P.X r a) ^ 2 * (deriv (fun u => dtilde P.X u a) r) ^ 2
        + 8 * (dtilde P.X r a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) r) r := by
    have h := (hd3.const_mul 8).mul hHD1
    convert h using 1; ring
  have hB0 := hBnum.div_const (6 * P.X * a)
  have hpieceB := hB0.mul hphi'
  -- piece C: C0(s)·φ'', C0 = d̃⁴/(6Xa)
  have hC0 := hd4.div_const (6 * P.X * a)
  have hpieceC := hC0.mul hphi''
  -- assemble
  have hsum : HasDerivAt (fun s => phif2 P.X a ℓ₁ ℓ₂ f s)
      ((24 * dtilde P.X r a * (deriv (fun u => dtilde P.X u a) r) ^ 3
            + 36 * (dtilde P.X r a) ^ 2 * deriv (fun u => dtilde P.X u a) r
                * iteratedDeriv 2 (fun u => dtilde P.X u a) r
            + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 3 (fun u => dtilde P.X u a) r)
          / (6 * P.X * a) * (f + phi P.X a ℓ₁ ℓ₂ r)
        + (36 * (dtilde P.X r a) ^ 2 * (deriv (fun u => dtilde P.X u a) r) ^ 2
            + 12 * (dtilde P.X r a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) r)
          / (6 * P.X * a) * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r
        + (12 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) / (6 * P.X * a)
          * iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r
        + (dtilde P.X r a) ^ 4 / (6 * P.X * a)
          * iteratedDeriv 3 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r := by
    have h := (hpieceA.add hpieceB).add hpieceC
    have heq : (fun s => phif2 P.X a ℓ₁ ℓ₂ f s)
        = (fun s => (12 * (dtilde P.X s a) ^ 2 * (deriv (fun u => dtilde P.X u a) s) ^ 2
                + 4 * (dtilde P.X s a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) s)
              / (6 * P.X * a) * (f + phi P.X a ℓ₁ ℓ₂ s)
            + (8 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) / (6 * P.X * a)
              * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s
            + (dtilde P.X s a) ^ 4 / (6 * P.X * a)
              * iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) s) := by
      funext s; rw [phif2]
    rw [heq]
    convert h using 1
    ring
  exact hsum.deriv

end Squarefree
