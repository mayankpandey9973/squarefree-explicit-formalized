import Squarefree.Lower.Step2Curvature

/-!
# §5 Step-2 BANDS: the second derivative `φ_f''` — differentiation infrastructure

This file builds the **second-derivative** differentiation infrastructure of the Step-2/3 phase
`φ_f` (the curvature lemmas `hmono`/`hlower` that *consume* it live in `Step2Curvature3`):

* `phi_deriv_hasDerivAt` — `s ↦ deriv (phi ·) s` is differentiable, with derivative
  `iteratedDeriv 2 phi`.  (Differentiate the closed first derivative `φ' = K·b̃·bracket/d̃⁶`.)
* `phif_deriv_hasDerivAt` — `s ↦ deriv (φ_f ·) s` is differentiable, with the product-rule
  second derivative `φ_f'' = (d̃⁴)''/(6Xa)·(f+φ) + 2(d̃⁴)'/(6Xa)·φ' + d̃⁴/(6Xa)·φ''`.
* `phif_iteratedDeriv2_eq` — the **explicit** product-rule value of `φ_f''`, with
  `(d̃⁴)'' = 12 d̃²(d̃')² + 4 d̃³ d̃''` the dominant sign-carrier.
* `phi_iteratedDeriv2_eq` — the explicit product/quotient-rule value of `φ''`.
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- The closed-form first derivative of `φ = phi X a ℓ₁ ℓ₂`, as a function of `s`
(matching `phi_hasDerivAt`): `φ'(s) = K·b̃(s)·bracket(s)/d̃(s)⁶`, with `K = 12ℓ₁ℓ₂(ℓ₂−ℓ₁)Xa`
and `bracket(s) = 2·b̃'(s)·d̃(s) − 5·b̃(s)·d̃'(s)`, where `b̃'(s) = (d̃'(s+ℓ₁) − d̃'(s))/ℓ₁`. -/
private noncomputable def phi1 (X a ℓ₁ ℓ₂ s : ℝ) : ℝ :=
  12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * X * a * bt X a ℓ₁ s
    * (2 * ((deriv (fun u => dtilde X u a) (s + ℓ₁)
              - deriv (fun u => dtilde X u a) s) / ℓ₁) * dtilde X s a
        - 5 * bt X a ℓ₁ s * deriv (fun u => dtilde X u a) s)
    / (dtilde X s a) ^ 6

/-- `deriv (phi ·) =ᶠ phi1 ·` near `r > 0` (with `r + ℓ₁ > 0`). -/
private theorem phi_deriv_eventuallyEq {P : Globals} {a ℓ₁ ℓ₂ r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    deriv (fun s => phi P.X a ℓ₁ ℓ₂ s) =ᶠ[nhds r] (fun s => phi1 P.X a ℓ₁ ℓ₂ s) := by
  have hU : {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} ∈ nhds r := by
    have hopen : IsOpen {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} := by
      have h1 : IsOpen {s : ℝ | 0 < s} := isOpen_lt continuous_const continuous_id
      have h2 : IsOpen {s : ℝ | 0 < s + ℓ₁} :=
        isOpen_lt continuous_const (continuous_id.add continuous_const)
      simpa [Set.setOf_and] using h1.inter h2
    exact hopen.mem_nhds ⟨hr0, hrl⟩
  refine Filter.eventuallyEq_of_mem hU ?_
  intro s hs
  rw [(phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hs.1 hs.2 hℓne).deriv]
  simp only [phi1]

/-- `phi1` is differentiable at `r > 0` (with `r + ℓ₁ > 0`).  Its derivative (kept symbolic
in `d̃, d̃', d̃''` via `deriv`/`iteratedDeriv 2`) is the value used to define `φ''`.  This is the
quotient/product-rule expansion of `φ' = K·b̃·bracket/d̃⁶`. -/
private theorem phi1_hasDerivAt {P : Globals} {a ℓ₁ ℓ₂ r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    HasDerivAt (fun s => phi1 P.X a ℓ₁ ℓ₂ s)
      (deriv (fun s => phi1 P.X a ℓ₁ ℓ₂ s) r) r := by
  -- HasDerivAt for d̃, d̃', and their shifts (kept symbolic in `deriv`/`iteratedDeriv 2`)
  have hHD0 : HasDerivAt (fun s => dtilde P.X s a)
      (deriv (fun u => dtilde P.X u a) r) r := by
    have h := dtilde_r_hasDerivAt (X := P.X) (a := a) (r := r) P.X_pos ha0 hr0
    rw [h.deriv]; exact h
  have hHD1 : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) s)
      (iteratedDeriv 2 (fun u => dtilde P.X u a) r) r :=
    dtilde_deriv_hasDerivAt (X := P.X) (a := a) (s := r) P.X_pos ha0 hr0
  have hshift : HasDerivAt (fun s => s + ℓ₁) 1 r := (hasDerivAt_id r).add_const ℓ₁
  have hHD1ℓ : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) (s + ℓ₁))
      (iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)) r := by
    have hbase := dtilde_deriv_hasDerivAt (X := P.X) (a := a) (s := r + ℓ₁) P.X_pos ha0 hrl
    have := hbase.comp r hshift
    simpa using this
  -- b̃ → b̃'(r) := (d̃'(r+ℓ₁) − d̃'(r))/ℓ₁
  have hbt : HasDerivAt (fun s => bt P.X a ℓ₁ s)
      ((deriv (fun u => dtilde P.X u a) (r + ℓ₁) - deriv (fun u => dtilde P.X u a) r) / ℓ₁) r :=
    bt_hasDerivAt (X := P.X) (a := a) (ℓ := ℓ₁) (r := r) P.X_pos ha0 hr0 hrl hℓne
  -- b̃'(s) := (d̃'(s+ℓ₁) − d̃'(s))/ℓ₁, deriv = (d̃''(r+ℓ₁) − d̃''(r))/ℓ₁
  have hbt' : HasDerivAt (fun s => (deriv (fun u => dtilde P.X u a) (s + ℓ₁)
        - deriv (fun u => dtilde P.X u a) s) / ℓ₁)
      ((iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)
        - iteratedDeriv 2 (fun u => dtilde P.X u a) r) / ℓ₁) r :=
    (hHD1ℓ.sub hHD1).div_const ℓ₁
  -- d̃⁶
  have hd6 : HasDerivAt (fun s => (dtilde P.X s a) ^ 6)
      (6 * (dtilde P.X r a) ^ 5 * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 6; simpa using this
  have hd0ne : dtilde P.X r a ≠ 0 := ne_of_gt (dtilde_pos P.X_pos ha0 hr0)
  have hd6ne : (dtilde P.X r a) ^ 6 ≠ 0 := pow_ne_zero 6 hd0ne
  -- bracket(s) = 2·b̃'(s)·d̃(s) − 5·b̃(s)·d̃'(s)
  have hbracket : HasDerivAt
      (fun s => 2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
            - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s)
      (deriv (fun s => 2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
            - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s) r) r := by
    have hterm1 := (hbt'.const_mul 2).mul hHD0
    have hterm2 := (hbt.const_mul 5).mul hHD1
    have h := hterm1.sub hterm2
    exact h.differentiableAt.hasDerivAt
  -- K · b̃ · bracket
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  have hKb : HasDerivAt (fun s => K * bt P.X a ℓ₁ s)
      (deriv (fun s => K * bt P.X a ℓ₁ s) r) r := (hbt.const_mul K).differentiableAt.hasDerivAt
  -- numerator N(s) = (K·b̃(s)) · bracket(s)
  have hnum : HasDerivAt
      (fun s => (K * bt P.X a ℓ₁ s)
        * (2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                  - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
            - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s))
      (deriv (fun s => (K * bt P.X a ℓ₁ s)
        * (2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                  - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
            - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s)) r) r :=
    (hKb.mul hbracket).differentiableAt.hasDerivAt
  -- quotient N / d̃⁶
  have hquot := hnum.div hd6 hd6ne
  -- phi1 equals that quotient as a function
  have hphi1_eq : (fun s => phi1 P.X a ℓ₁ ℓ₂ s)
      = (fun s => (K * bt P.X a ℓ₁ s)
          * (2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                    - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
              - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s)
          / (dtilde P.X s a) ^ 6) := by
    funext s; rw [phi1, hK_def]
  rw [hphi1_eq]
  exact hquot.differentiableAt.hasDerivAt

/-- **`deriv φ` is differentiable, with derivative `iteratedDeriv 2 φ`** (`φ = phi …`).  This
exposes the MVT-ready differentiability of the §5 Step-1 phase derivative, used for the §5
Step-2 second-derivative product rule. -/
theorem phi_deriv_hasDerivAt {P : Globals} {a ℓ₁ ℓ₂ r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    HasDerivAt (fun s => deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      (iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r := by
  -- `iteratedDeriv 2 phi r = deriv (deriv phi) r = deriv phi1 r`
  have hee := phi_deriv_eventuallyEq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  have hid2 : iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r
      = deriv (fun s => phi1 P.X a ℓ₁ ℓ₂ s) r := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hee.deriv_eq]
  rw [hid2]
  -- `deriv phi =ᶠ phi1`; transport the `phi1` differentiability
  exact (phi1_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne).congr_of_eventuallyEq
    hee

/-- The closed-form first derivative of `φ_f = phif X a ℓ₁ ℓ₂ f`, as a function of `s`
(matching `phif_hasDerivAt`):
`φ_f'(s) = 4d̃³d̃'/(6Xa)·(f+φ) + d̃⁴/(6Xa)·φ'`. -/
private noncomputable def phif1 (X a ℓ₁ ℓ₂ f s : ℝ) : ℝ :=
  (4 * (dtilde X s a) ^ 3 * deriv (fun u => dtilde X u a) s) / (6 * X * a)
      * (f + phi X a ℓ₁ ℓ₂ s)
    + (dtilde X s a) ^ 4 / (6 * X * a) * deriv (fun u => phi X a ℓ₁ ℓ₂ u) s

/-- `deriv (φ_f ·) =ᶠ phif1 ·` near `r > 0` (with `r + ℓ₁ > 0`). -/
private theorem phif_deriv_eventuallyEq {P : Globals} {a ℓ₁ ℓ₂ f r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    deriv (fun s => phif P.X a ℓ₁ ℓ₂ f s) =ᶠ[nhds r] (fun s => phif1 P.X a ℓ₁ ℓ₂ f s) := by
  have hU : {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} ∈ nhds r := by
    have hopen : IsOpen {s : ℝ | 0 < s ∧ 0 < s + ℓ₁} := by
      have h1 : IsOpen {s : ℝ | 0 < s} := isOpen_lt continuous_const continuous_id
      have h2 : IsOpen {s : ℝ | 0 < s + ℓ₁} :=
        isOpen_lt continuous_const (continuous_id.add continuous_const)
      simpa [Set.setOf_and] using h1.inter h2
    exact hopen.mem_nhds ⟨hr0, hrl⟩
  refine Filter.eventuallyEq_of_mem hU ?_
  intro s hs
  rw [(phif_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f) ha0 hs.1 hs.2 hℓne).deriv]
  simp only [phif1]

/-- **`deriv φ_f` is differentiable, with derivative `iteratedDeriv 2 φ_f`** (`φ_f = phif …`).
This is the §5 Step-2 second derivative.  The value is kept symbolic in
`d̃, d̃', d̃''` (`deriv`/`iteratedDeriv 2` of `dtilde`) and `φ, φ', φ''` (of `phi`). -/
theorem phif_deriv_hasDerivAt {P : Globals} {a ℓ₁ ℓ₂ f r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    HasDerivAt (fun s => deriv (fun u => phif P.X a ℓ₁ ℓ₂ f u) s)
      (iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r) r := by
  have hee := phif_deriv_eventuallyEq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    ha0 hr0 hrl hℓne
  have hid2 : iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r
      = deriv (fun s => phif1 P.X a ℓ₁ ℓ₂ f s) r := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hee.deriv_eq]
  rw [hid2]
  -- differentiate phif1
  -- HasDerivAt facts for d̃, d̃', φ, φ'
  have hHD0 : HasDerivAt (fun s => dtilde P.X s a)
      (deriv (fun u => dtilde P.X u a) r) r := by
    have h := dtilde_r_hasDerivAt (X := P.X) (a := a) (r := r) P.X_pos ha0 hr0
    rw [h.deriv]; exact h
  have hHD1 : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) s)
      (iteratedDeriv 2 (fun u => dtilde P.X u a) r) r :=
    dtilde_deriv_hasDerivAt (X := P.X) (a := a) (s := r) P.X_pos ha0 hr0
  have hphi : HasDerivAt (fun s => phi P.X a ℓ₁ ℓ₂ s)
      (deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    (phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne).differentiableAt.hasDerivAt
  have hphi' : HasDerivAt (fun s => deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      (iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    phi_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  -- 6Xa ≠ 0
  have h6Xa : (6 : ℝ) * P.X * a ≠ 0 := by have := P.X_pos; positivity
  -- piece A: 4·d̃³·d̃'/(6Xa)·(f+φ)
  have hA1 : HasDerivAt (fun s => 4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s)
      (deriv (fun s => 4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) r) r := by
    have hcube : HasDerivAt (fun s => 4 * (dtilde P.X s a) ^ 3)
        (4 * (3 * (dtilde P.X r a) ^ 2 * deriv (fun u => dtilde P.X u a) r)) r := by
      have := (hHD0.pow 3).const_mul 4; simpa using this
    exact (hcube.mul hHD1).differentiableAt.hasDerivAt
  have hAdiv : HasDerivAt
      (fun s => (4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) / (6 * P.X * a))
      (deriv (fun s => (4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s)
        / (6 * P.X * a)) r) r :=
    (hA1.div_const (6 * P.X * a)).differentiableAt.hasDerivAt
  have hfphi : HasDerivAt (fun s => f + phi P.X a ℓ₁ ℓ₂ s)
      (deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r := hphi.const_add f
  have hpieceA : HasDerivAt
      (fun s => (4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) / (6 * P.X * a)
        * (f + phi P.X a ℓ₁ ℓ₂ s))
      (deriv (fun s => (4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s)
          / (6 * P.X * a) * (f + phi P.X a ℓ₁ ℓ₂ s)) r) r :=
    (hAdiv.mul hfphi).differentiableAt.hasDerivAt
  -- piece B: d̃⁴/(6Xa)·φ'
  have hd4 : HasDerivAt (fun s => (dtilde P.X s a) ^ 4)
      (4 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 4; simpa using this
  have hd4div : HasDerivAt (fun s => (dtilde P.X s a) ^ 4 / (6 * P.X * a))
      (deriv (fun s => (dtilde P.X s a) ^ 4 / (6 * P.X * a)) r) r :=
    (hd4.div_const (6 * P.X * a)).differentiableAt.hasDerivAt
  have hpieceB : HasDerivAt
      (fun s => (dtilde P.X s a) ^ 4 / (6 * P.X * a) * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      (deriv (fun s => (dtilde P.X s a) ^ 4 / (6 * P.X * a)
          * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s) r) r :=
    (hd4div.mul hphi').differentiableAt.hasDerivAt
  -- sum
  have hsum : HasDerivAt (fun s => phif1 P.X a ℓ₁ ℓ₂ f s)
      (deriv (fun s => phif1 P.X a ℓ₁ ℓ₂ f s) r) r := by
    have h := hpieceA.add hpieceB
    have heq : (fun s => phif1 P.X a ℓ₁ ℓ₂ f s)
        = (fun s => (4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) / (6 * P.X * a)
              * (f + phi P.X a ℓ₁ ℓ₂ s)
            + (dtilde P.X s a) ^ 4 / (6 * P.X * a) * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s) := by
      funext s; rw [phif1]
    rw [heq]
    exact h.differentiableAt.hasDerivAt
  exact hsum.congr_of_eventuallyEq hee

/-- **The explicit product-rule value of `φ_f''`** (writeup line 924 region).  Abbreviating
`d̃, d̃' = deriv d̃, d̃'' = iteratedDeriv 2 d̃` and `φ, φ' = deriv φ, φ'' = iteratedDeriv 2 φ`,

  `φ_f'' = ((12 d̃²(d̃')² + 4 d̃³ d̃'')/(6Xa))·(f+φ) + (8 d̃³ d̃'/(6Xa))·φ' + (d̃⁴/(6Xa))·φ''`,

with `(d̃⁴)'' = 12 d̃²(d̃')² + 4 d̃³ d̃'' > 0` the dominant sign-carrier. -/
theorem phif_iteratedDeriv2_eq {P : Globals} {a ℓ₁ ℓ₂ f r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r
      = (12 * (dtilde P.X r a) ^ 2 * (deriv (fun u => dtilde P.X u a) r) ^ 2
            + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) r)
          / (6 * P.X * a) * (f + phi P.X a ℓ₁ ℓ₂ r)
        + (8 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) / (6 * P.X * a)
          * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r
        + (dtilde P.X r a) ^ 4 / (6 * P.X * a)
          * iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r := by
  -- `iteratedDeriv 2 φ_f r = deriv phif1 r`
  have hee := phif_deriv_eventuallyEq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) (f := f)
    ha0 hr0 hrl hℓne
  have hid2 : iteratedDeriv 2 (fun u => phif P.X a ℓ₁ ℓ₂ f u) r
      = deriv (fun s => phif1 P.X a ℓ₁ ℓ₂ f s) r := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hee.deriv_eq]
  rw [hid2]
  -- HasDerivAt facts for d̃, d̃', φ, φ'
  have hHD0 : HasDerivAt (fun s => dtilde P.X s a)
      (deriv (fun u => dtilde P.X u a) r) r := by
    have h := dtilde_r_hasDerivAt (X := P.X) (a := a) (r := r) P.X_pos ha0 hr0
    rw [h.deriv]; exact h
  have hHD1 : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) s)
      (iteratedDeriv 2 (fun u => dtilde P.X u a) r) r :=
    dtilde_deriv_hasDerivAt (X := P.X) (a := a) (s := r) P.X_pos ha0 hr0
  have hphi : HasDerivAt (fun s => phi P.X a ℓ₁ ℓ₂ s)
      (deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    (phi_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne).differentiableAt.hasDerivAt
  have hphi' : HasDerivAt (fun s => deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      (iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    phi_deriv_hasDerivAt (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  have h6Xa : (6 : ℝ) * P.X * a ≠ 0 := by have := P.X_pos; positivity
  -- piece A: A(s) = 4·d̃³·d̃'/(6Xa), with A'(r) = (12 d̃²(d̃')² + 4 d̃³ d̃'')/(6Xa)
  have hA1 : HasDerivAt (fun s => 4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s)
      (12 * (dtilde P.X r a) ^ 2 * (deriv (fun u => dtilde P.X u a) r) ^ 2
        + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) r) r := by
    have hcube : HasDerivAt (fun s => 4 * (dtilde P.X s a) ^ 3)
        (4 * (3 * (dtilde P.X r a) ^ 2 * deriv (fun u => dtilde P.X u a) r)) r := by
      have := (hHD0.pow 3).const_mul 4; simpa using this
    have h := hcube.mul hHD1
    convert h using 1; ring
  have hAdiv : HasDerivAt
      (fun s => (4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) / (6 * P.X * a))
      ((12 * (dtilde P.X r a) ^ 2 * (deriv (fun u => dtilde P.X u a) r) ^ 2
        + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) r)
        / (6 * P.X * a)) r := hA1.div_const (6 * P.X * a)
  have hfphi : HasDerivAt (fun s => f + phi P.X a ℓ₁ ℓ₂ s)
      (deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r := hphi.const_add f
  have hpieceA : HasDerivAt
      (fun s => (4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) / (6 * P.X * a)
        * (f + phi P.X a ℓ₁ ℓ₂ s))
      ((12 * (dtilde P.X r a) ^ 2 * (deriv (fun u => dtilde P.X u a) r) ^ 2
          + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) r)
          / (6 * P.X * a) * (f + phi P.X a ℓ₁ ℓ₂ r)
        + (4 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) / (6 * P.X * a)
          * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r := hAdiv.mul hfphi
  -- piece B: B(s) = d̃⁴/(6Xa)·φ'(s), with B'(r) = (4 d̃³ d̃'/(6Xa))·φ' + (d̃⁴/(6Xa))·φ''
  have hd4 : HasDerivAt (fun s => (dtilde P.X s a) ^ 4)
      (4 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 4; simpa using this
  have hd4div : HasDerivAt (fun s => (dtilde P.X s a) ^ 4 / (6 * P.X * a))
      ((4 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) / (6 * P.X * a)) r :=
    hd4.div_const (6 * P.X * a)
  have hpieceB : HasDerivAt
      (fun s => (dtilde P.X s a) ^ 4 / (6 * P.X * a) * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s)
      ((4 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) / (6 * P.X * a)
          * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r
        + (dtilde P.X r a) ^ 4 / (6 * P.X * a) * iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r :=
    hd4div.mul hphi'
  -- sum, identify with phif1
  have hsum : HasDerivAt (fun s => phif1 P.X a ℓ₁ ℓ₂ f s)
      ((12 * (dtilde P.X r a) ^ 2 * (deriv (fun u => dtilde P.X u a) r) ^ 2
            + 4 * (dtilde P.X r a) ^ 3 * iteratedDeriv 2 (fun u => dtilde P.X u a) r)
          / (6 * P.X * a) * (f + phi P.X a ℓ₁ ℓ₂ r)
        + (8 * (dtilde P.X r a) ^ 3 * deriv (fun u => dtilde P.X u a) r) / (6 * P.X * a)
          * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) r
        + (dtilde P.X r a) ^ 4 / (6 * P.X * a)
          * iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r) r := by
    have h := hpieceA.add hpieceB
    have heq : (fun s => phif1 P.X a ℓ₁ ℓ₂ f s)
        = (fun s => (4 * (dtilde P.X s a) ^ 3 * deriv (fun u => dtilde P.X u a) s) / (6 * P.X * a)
              * (f + phi P.X a ℓ₁ ℓ₂ s)
            + (dtilde P.X s a) ^ 4 / (6 * P.X * a) * deriv (fun u => phi P.X a ℓ₁ ℓ₂ u) s) := by
      funext s; rw [phif1]
    rw [heq]
    convert h using 1
    ring
  exact hsum.deriv

/-- **The explicit product/quotient-rule value of `φ''`** (`φ = phi …`).  Abbreviating
`d, d1 = d̃', d2 = d̃''` and `b = b̃, bp = b̃' = (d̃'(r+ℓ₁)−d̃'(r))/ℓ₁,
bd = b̃'' = (d̃''(r+ℓ₁)−d̃''(r))/ℓ₁`, with `bracket = 2 bp d − 5 b d1`,

  `φ'' = K·( bp·bracket + b·(2 bd d − 3 bp d1 − 5 b d2) − 6 b·bracket·d1/d ) / d⁶`. -/
theorem phi_iteratedDeriv2_eq {P : Globals} {a ℓ₁ ℓ₂ r : ℝ}
    (ha0 : 0 < a) (hr0 : 0 < r) (hrl : 0 < r + ℓ₁) (hℓne : ℓ₁ ≠ 0) :
    iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r
      = (12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a)
        * ( ((deriv (fun u => dtilde P.X u a) (r + ℓ₁)
                - deriv (fun u => dtilde P.X u a) r) / ℓ₁)
              * (2 * ((deriv (fun u => dtilde P.X u a) (r + ℓ₁)
                    - deriv (fun u => dtilde P.X u a) r) / ℓ₁) * dtilde P.X r a
                - 5 * bt P.X a ℓ₁ r * deriv (fun u => dtilde P.X u a) r)
            + bt P.X a ℓ₁ r
              * (2 * ((iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)
                    - iteratedDeriv 2 (fun u => dtilde P.X u a) r) / ℓ₁) * dtilde P.X r a
                  - 3 * ((deriv (fun u => dtilde P.X u a) (r + ℓ₁)
                    - deriv (fun u => dtilde P.X u a) r) / ℓ₁) * deriv (fun u => dtilde P.X u a) r
                  - 5 * bt P.X a ℓ₁ r * iteratedDeriv 2 (fun u => dtilde P.X u a) r)
            - 6 * bt P.X a ℓ₁ r
                * (2 * ((deriv (fun u => dtilde P.X u a) (r + ℓ₁)
                      - deriv (fun u => dtilde P.X u a) r) / ℓ₁) * dtilde P.X r a
                  - 5 * bt P.X a ℓ₁ r * deriv (fun u => dtilde P.X u a) r)
                * deriv (fun u => dtilde P.X u a) r / dtilde P.X r a )
        / (dtilde P.X r a) ^ 6 := by
  -- `iteratedDeriv 2 φ r = deriv phi1 r`
  have hee := phi_deriv_eventuallyEq (P := P) (a := a) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) ha0 hr0 hrl hℓne
  have hid2 : iteratedDeriv 2 (fun u => phi P.X a ℓ₁ ℓ₂ u) r
      = deriv (fun s => phi1 P.X a ℓ₁ ℓ₂ s) r := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hee.deriv_eq]
  rw [hid2]
  -- symbolic derivative facts
  have hHD0 : HasDerivAt (fun s => dtilde P.X s a)
      (deriv (fun u => dtilde P.X u a) r) r := by
    have h := dtilde_r_hasDerivAt (X := P.X) (a := a) (r := r) P.X_pos ha0 hr0
    rw [h.deriv]; exact h
  have hHD1 : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) s)
      (iteratedDeriv 2 (fun u => dtilde P.X u a) r) r :=
    dtilde_deriv_hasDerivAt (X := P.X) (a := a) (s := r) P.X_pos ha0 hr0
  have hshift : HasDerivAt (fun s => s + ℓ₁) 1 r := (hasDerivAt_id r).add_const ℓ₁
  have hHD1ℓ : HasDerivAt (fun s => deriv (fun u => dtilde P.X u a) (s + ℓ₁))
      (iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)) r := by
    have hbase := dtilde_deriv_hasDerivAt (X := P.X) (a := a) (s := r + ℓ₁) P.X_pos ha0 hrl
    have := hbase.comp r hshift
    simpa using this
  have hbt : HasDerivAt (fun s => bt P.X a ℓ₁ s)
      ((deriv (fun u => dtilde P.X u a) (r + ℓ₁) - deriv (fun u => dtilde P.X u a) r) / ℓ₁) r :=
    bt_hasDerivAt (X := P.X) (a := a) (ℓ := ℓ₁) (r := r) P.X_pos ha0 hr0 hrl hℓne
  have hbt' : HasDerivAt (fun s => (deriv (fun u => dtilde P.X u a) (s + ℓ₁)
        - deriv (fun u => dtilde P.X u a) s) / ℓ₁)
      ((iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)
        - iteratedDeriv 2 (fun u => dtilde P.X u a) r) / ℓ₁) r :=
    (hHD1ℓ.sub hHD1).div_const ℓ₁
  have hd6 : HasDerivAt (fun s => (dtilde P.X s a) ^ 6)
      (6 * (dtilde P.X r a) ^ 5 * deriv (fun u => dtilde P.X u a) r) r := by
    have := hHD0.pow 6; simpa using this
  have hd0ne : dtilde P.X r a ≠ 0 := ne_of_gt (dtilde_pos P.X_pos ha0 hr0)
  have hd6ne : (dtilde P.X r a) ^ 6 ≠ 0 := pow_ne_zero 6 hd0ne
  -- abbreviations
  set d := dtilde P.X r a with hd_def
  set d1 := deriv (fun u => dtilde P.X u a) r with hd1_def
  set d2 := iteratedDeriv 2 (fun u => dtilde P.X u a) r with hd2_def
  set b := bt P.X a ℓ₁ r with hb_def
  set bp := (deriv (fun u => dtilde P.X u a) (r + ℓ₁) - deriv (fun u => dtilde P.X u a) r) / ℓ₁
    with hbp_def
  set bd := (iteratedDeriv 2 (fun u => dtilde P.X u a) (r + ℓ₁)
    - iteratedDeriv 2 (fun u => dtilde P.X u a) r) / ℓ₁ with hbd_def
  set K := 12 * ℓ₁ * ℓ₂ * (ℓ₂ - ℓ₁) * P.X * a with hK_def
  -- bracket(s) := 2·b̃'(s)·d̃(s) − 5·b̃(s)·d̃'(s)
  have hbracket : HasDerivAt
      (fun s => 2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
            - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s)
      ((2 * bd * d + 2 * bp * d1) - (5 * bp * d1 + 5 * b * d2)) r := by
    have hterm1 := (hbt'.const_mul 2).mul hHD0
    have hterm2 := (hbt.const_mul 5).mul hHD1
    have h := hterm1.sub hterm2
    convert h using 1
  -- numerator N(s) = (K·b̃(s)) · bracket(s)
  set bracket := 2 * bp * d - 5 * b * d1 with hbracket_def
  have hKb : HasDerivAt (fun s => K * bt P.X a ℓ₁ s) (K * bp) r := by
    have := hbt.const_mul K; convert this using 1
  have hnum : HasDerivAt
      (fun s => (K * bt P.X a ℓ₁ s)
        * (2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                  - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
            - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s))
      ((K * bp) * bracket + (K * b) * ((2 * bd * d + 2 * bp * d1) - (5 * bp * d1 + 5 * b * d2))) r := by
    have h := hKb.mul hbracket
    convert h using 1
  -- quotient N / d̃⁶
  have hquot := hnum.div hd6 hd6ne
  have hphi1_deriv : HasDerivAt (fun s => phi1 P.X a ℓ₁ ℓ₂ s)
      (((((K * bp) * bracket + (K * b) * ((2 * bd * d + 2 * bp * d1) - (5 * bp * d1 + 5 * b * d2)))
          * (dtilde P.X r a) ^ 6
        - (K * b * bracket) * (6 * (dtilde P.X r a) ^ 5 * deriv (fun u => dtilde P.X u a) r))
          / ((dtilde P.X r a) ^ 6) ^ 2)) r := by
    have heq : (fun s => phi1 P.X a ℓ₁ ℓ₂ s)
        = (fun s => (K * bt P.X a ℓ₁ s)
            * (2 * ((deriv (fun u => dtilde P.X u a) (s + ℓ₁)
                      - deriv (fun u => dtilde P.X u a) s) / ℓ₁) * dtilde P.X s a
                - 5 * bt P.X a ℓ₁ s * deriv (fun u => dtilde P.X u a) s)
            / (dtilde P.X s a) ^ 6) := by
      funext s; rw [phi1, hK_def]
    rw [heq, hbracket_def]
    exact hquot
  rw [hphi1_deriv.deriv, hbracket_def]
  -- algebraic reconciliation of the two rational expressions
  have hd0ne' : d ≠ 0 := hd0ne
  simp only [hd_def, hd1_def, hd2_def, hb_def, hbp_def, hbd_def, hK_def] at hd0ne' ⊢
  field_simp
  ring

end Squarefree
