import Squarefree.Counting.FourthDeriv
import Squarefree.Main
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# §2 short-Δ regime: helpers for Prop 2.4

Private calculus / arithmetic lemmas used by `Squarefree.prop_2_4` (`Squarefree/ShortDelta.lean`):
the 4th derivative of `f = X·x⁻²`, its size bounds on `[D,3D]`, the `dCard → distInt`-count
bridge, and the four `X`-exponent budget bounds.  See `../explicit_writeup.md` 209–241 and
`math_audit.md` §2.
-/

open Classical Set Finset Squarefree.Counting

namespace Squarefree.ShortDeltaAux

/-- The model curve `f(x) = X·x⁻²` (`= X/x²` on positives). -/
noncomputable def fcurve (X : ℝ) : ℝ → ℝ := fun x => X * x ^ (-2 : ℤ)

/-- `fcurve X x = X / x²`. -/
theorem fcurve_eq (X x : ℝ) : fcurve X x = X / x ^ 2 := by
  rw [fcurve, show (-2 : ℤ) = -(2 : ℕ) by norm_num, zpow_neg, zpow_natCast]; ring

/-- The 4th derivative of `X·x⁻²` is `120·X·x⁻⁶`. -/
theorem iteratedDeriv_four_fcurve (X x : ℝ) :
    iteratedDeriv 4 (fcurve X) x = 120 * X * x ^ (-6 : ℤ) := by
  show iteratedDeriv 4 (fun x : ℝ => X * x ^ (-2 : ℤ)) x = _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_zpow']
  norm_num
  ring

/-- `fcurve X` is `C⁴` on `(0, 4N)` for `0 < N`. -/
theorem contDiffOn_fcurve (X N : ℝ) :
    ContDiffOn ℝ 4 (fcurve X) (Ioo 0 (4 * N)) := by
  have hfun : fcurve X = fun x : ℝ => X * (x ^ 2)⁻¹ := by
    funext x; rw [fcurve, show (-2 : ℤ) = -(2 : ℕ) by norm_num, zpow_neg, zpow_natCast]
  rw [hfun]
  apply ContDiffOn.mul contDiffOn_const
  apply ContDiffOn.inv (contDiffOn_id.pow 2)
  intro x hx; have : 0 < x := hx.1; positivity

/-- `dCard → distInt`-count bridge core: a `d ≥ D` with some `m·d² ∈ [X,X+H]` has
`‖X/d²‖ ≤ H/D²`. -/
theorem distInt_le_of_mem (X H D : ℝ) (hD : 0 < D) (hH : 0 ≤ H) (d : ℤ) (hd : D ≤ (d : ℝ))
    (m : ℤ) (h1 : X ≤ (m : ℝ) * (d : ℝ) ^ 2) (h2 : (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H) :
    distInt (fcurve X (d : ℝ)) ≤ H / D ^ 2 := by
  have hdpos : (0 : ℝ) < (d : ℝ) := lt_of_lt_of_le hD hd
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  rw [distInt, fcurve_eq]
  refine le_trans (round_le (X / (d : ℝ) ^ 2) m) ?_
  have hle1 : |X / (d : ℝ) ^ 2 - (m : ℝ)| ≤ H / (d : ℝ) ^ 2 := by
    have hrw : X / (d : ℝ) ^ 2 - (m : ℝ) = (X - (m : ℝ) * (d : ℝ) ^ 2) / (d : ℝ) ^ 2 := by
      field_simp
    rw [hrw, abs_div, abs_of_pos hd2]
    gcongr
    rw [abs_le]; constructor <;> nlinarith [h1, h2]
  refine le_trans hle1 ?_
  gcongr

/-- Lower 4th-derivative bound on `[D,3D]`: with `Λ = 120X/(729 D⁶)`, `Λ ≤ |f⁗ x|`. -/
theorem lambda_le_absDeriv (X D : ℝ) (hX : 0 < X) (hD : 0 < D) (x : ℝ)
    (hx : x ∈ Set.Icc D (3 * D)) :
    120 * X / (729 * D ^ 6) ≤ |iteratedDeriv 4 (fcurve X) x| := by
  have hxpos : 0 < x := lt_of_lt_of_le hD hx.1
  have hx3 : x ≤ 3 * D := hx.2
  rw [iteratedDeriv_four_fcurve]
  have hval : (120 : ℝ) * X * x ^ (-6 : ℤ) = 120 * X / x ^ 6 := by
    rw [show (-6 : ℤ) = -(6 : ℕ) by norm_num, zpow_neg, zpow_natCast]; ring
  rw [hval, abs_of_pos (by positivity)]
  have hx6 : x ^ 6 ≤ 729 * D ^ 6 := by
    have h := pow_le_pow_left₀ hxpos.le hx3 6
    nlinarith [h]
  have hxp6 : (0 : ℝ) < x ^ 6 := by positivity
  rw [div_le_div_iff_of_pos_left (a := 120 * X) (by positivity) (by positivity) hxp6]
  exact hx6

/-- Upper 4th-derivative bound on `[D,3D]`: `|f⁗ x| ≤ 729·Λ` with `K = 729`. -/
theorem absDeriv_le_K_lambda (X D : ℝ) (hX : 0 < X) (hD : 0 < D) (x : ℝ)
    (hx : x ∈ Set.Icc D (3 * D)) :
    |iteratedDeriv 4 (fcurve X) x| ≤ 729 * (120 * X / (729 * D ^ 6)) := by
  have hxpos : 0 < x := lt_of_lt_of_le hD hx.1
  have hxD : D ≤ x := hx.1
  rw [iteratedDeriv_four_fcurve]
  have hval : (120 : ℝ) * X * x ^ (-6 : ℤ) = 120 * X / x ^ 6 := by
    rw [show (-6 : ℤ) = -(6 : ℕ) by norm_num, zpow_neg, zpow_natCast]; ring
  rw [hval, abs_of_pos (by positivity)]
  have hd6 : D ^ 6 ≤ x ^ 6 := by gcongr
  rw [div_le_iff₀ (by positivity)]
  have hxp6 : (0 : ℝ) < x ^ 6 := by positivity
  rw [show (729 : ℝ) * (120 * X / (729 * D ^ 6)) = 120 * X / D ^ 6 by
        field_simp]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [hX, hd6, pow_pos hD 6]

/-- `dCard` equals the `ℤ`-level filter cardinality (the `ℝ`-valued index set in `dCard`
is the injective image of `Icc ⌈D⌉ ⌊2D⌋ : Finset ℤ`). -/
theorem dCard_eq_int (X H D : ℝ) :
    Squarefree.dCard X H D
      = ((Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter
          (fun d : ℤ => ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H)).card := by
  rw [Squarefree.dCard]
  have hcast : (do let a ← Finset.Icc ⌈D⌉ ⌊2 * D⌋; pure ((a : ℝ)))
      = (Finset.Icc ⌈D⌉ ⌊2 * D⌋).image (fun a : ℤ => (a : ℝ)) := by
    rw [bind_pure_comp]; rfl
  rw [hcast, Finset.filter_image,
      Finset.card_image_of_injective _ (fun a b => by exact_mod_cast id)]

/-- `dCard → distInt`-count bridge: `dCard ≤ #{d ∈ (⌊D⌋,⌊2D⌋] : ‖X/d²‖ ≤ H/D²} + 1`. -/
theorem dCard_le_distCount (X H D : ℝ) (hD : 0 < D) (hH : 0 ≤ H) :
    (Squarefree.dCard X H D : ℝ)
      ≤ (((Finset.Ioc ⌊D⌋ ⌊2 * D⌋).filter
          (fun n : ℤ => distInt (fcurve X (n : ℝ)) ≤ H / D ^ 2)).card : ℝ) + 1 := by
  have hsub : (Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter
        (fun d : ℤ => ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H)
      ⊆ insert ⌊D⌋ ((Finset.Ioc ⌊D⌋ ⌊2 * D⌋).filter
          (fun n : ℤ => distInt (fcurve X (n : ℝ)) ≤ H / D ^ 2)) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hdc, hd2⟩, m, h1, h2⟩ := hd
    have hdgeD : D ≤ (d : ℝ) := le_trans (Int.le_ceil D) (by exact_mod_cast hdc)
    have hQd : distInt (fcurve X (d : ℝ)) ≤ H / D ^ 2 :=
      distInt_le_of_mem X H D hD hH d hdgeD m h1 h2
    rw [Finset.mem_insert]
    rcases lt_or_eq_of_le (le_trans (Int.floor_le_ceil D) hdc) with hlt | heq
    · right; rw [Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨hlt, hd2⟩, hQd⟩
    · left; exact heq.symm
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  rw [dCard_eq_int]
  calc (((Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter
          (fun d : ℤ => ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H)).card : ℝ)
      ≤ (((Finset.Ioc ⌊D⌋ ⌊2 * D⌋).filter
          (fun n : ℤ => distInt (fcurve X (n : ℝ)) ≤ H / D ^ 2)).card + 1 : ℕ) := by
        exact_mod_cast hcard
    _ = _ := by push_cast; ring

/-- Small-`D` trivial cardinality bound: `dCard ≤ D + 1`. -/
theorem dCard_le_card (X H D : ℝ) (hD : 0 < D) : (Squarefree.dCard X H D : ℝ) ≤ D + 1 := by
  rw [dCard_eq_int]
  have hfle : (((Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter
        (fun d : ℤ => ∃ m : ℤ, X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ X + H)).card : ℝ)
      ≤ ((Finset.Icc ⌈D⌉ ⌊2 * D⌋).card : ℝ) := by
    exact_mod_cast Finset.card_filter_le _ _
  refine le_trans hfle ?_
  rw [Int.card_Icc]
  have hge : (0 : ℤ) ≤ ⌊2 * D⌋ + 1 - ⌈D⌉ := by
    have h1 : ⌊D⌋ ≤ ⌊2 * D⌋ := Int.floor_le_floor (by linarith)
    have h2 : ⌈D⌉ ≤ ⌊D⌋ + 1 := Int.ceil_le_floor_add_one D
    omega
  have hc : (((⌊2 * D⌋ + 1 - ⌈D⌉).toNat : ℕ) : ℝ) = ((⌊2 * D⌋ + 1 - ⌈D⌉ : ℤ) : ℝ) := by
    have : (((⌊2 * D⌋ + 1 - ⌈D⌉).toNat : ℤ) : ℝ) = ((⌊2 * D⌋ + 1 - ⌈D⌉ : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg hge]
    exact_mod_cast this
  rw [hc]; push_cast
  have hb : (⌊2 * D⌋ : ℝ) ≤ 2 * D := Int.floor_le _
  have hcl : D ≤ (⌈D⌉ : ℝ) := Int.le_ceil _
  linarith

/-! ### Budget bounds for the four `fourthDeriv_count` terms

Throughout: `X ≥ 1`, `H = X^a > 0`, `0 < D ≤ X^b`, `δ = H/D²`, `Λ = 120X/(729D⁶)`.
Each term `T` is bounded `T ≤ C · X^a / X^u` from an exponent inequality `e ≤ a - u`. -/

open Real

/-- Generic combine: `T ≤ c·X^e` and `e ≤ a-u` give `T ≤ c·(X^a/X^u)`. -/
private theorem budget_combine {T c X e a u : ℝ} (hX : 1 ≤ X) (hc : 0 ≤ c)
    (hT : T ≤ c * X ^ e) (he : e ≤ a - u) : T ≤ c * (X ^ a / X ^ u) := by
  refine le_trans hT ?_
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  rw [← rpow_sub hXpos]; gcongr

/-- Term 1: `D^{7/8} ≤ X^{7b/8}`. -/
theorem term1_bound {X D a u : ℝ} (hX : 1 ≤ X) (b : ℝ) (hD : 0 < D)
    (hDb : D ≤ X ^ b) (he : b * (7 / 8) ≤ a - u) :
    D ^ (7 / 8 : ℝ) ≤ (1 : ℝ) * (X ^ a / X ^ u) := by
  apply budget_combine hX (by norm_num)
  · rw [one_mul]
    calc D ^ (7 / 8 : ℝ) ≤ (X ^ b) ^ (7 / 8 : ℝ) := rpow_le_rpow hD.le hDb (by norm_num)
      _ = X ^ (b * (7 / 8 : ℝ)) := by rw [← rpow_mul (by linarith)]
  · exact he

/-- Term 2: `D·δ^{1/8} = H^{1/8}D^{3/4} ≤ X^{a/8 + 3b/4}`. -/
theorem term2_bound {X H D a u : ℝ} (hX : 1 ≤ X) (b : ℝ) (hH : H = X ^ a)
    (hD : 0 < D) (hDb : D ≤ X ^ b)
    (he : a * (1 / 8) + b * (3 / 4) ≤ a - u) :
    D * (H / D ^ 2) ^ (1 / 8 : ℝ) ≤ (1 : ℝ) * (X ^ a / X ^ u) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hHpos : 0 < H := by rw [hH]; positivity
  apply budget_combine hX (by norm_num)
  rotate_left
  · exact he
  rw [one_mul]
  -- exact identity then bound
  have hid : D * (H / D ^ 2) ^ (1 / 8 : ℝ) = H ^ (1 / 8 : ℝ) * D ^ (3 / 4 : ℝ) := by
    have hd2 : (D ^ 2 : ℝ) ^ (1 / 8 : ℝ) = D ^ (1 / 4 : ℝ) := by
      rw [← rpow_natCast D 2, ← rpow_mul hD.le]; norm_num
    have hd34 : D * (D ^ (1 / 4 : ℝ))⁻¹ = D ^ (3 / 4 : ℝ) := by
      rw [← rpow_neg hD.le]; nth_rewrite 1 [← rpow_one D]; rw [← rpow_add hD]; norm_num
    rw [div_rpow hHpos.le (by positivity), hd2, div_eq_mul_inv, ← mul_assoc,
        mul_comm D, mul_assoc, hd34]
  rw [hid, hH]
  calc (X ^ a) ^ (1 / 8 : ℝ) * D ^ (3 / 4 : ℝ)
      ≤ (X ^ a) ^ (1 / 8 : ℝ) * (X ^ b) ^ (3 / 4 : ℝ) := by
        gcongr
    _ = X ^ (a * (1 / 8 : ℝ) + b * (3 / 4 : ℝ)) := by
        rw [← rpow_mul hXpos.le, ← rpow_mul hXpos.le, ← rpow_add hXpos]

/-- Term 3: `D^{7/8}(δ/Λ)^{1/8} ≤ 7^{1/8}·X^{-1/8 + a/8 + 11b/8}`. -/
theorem term3_bound {X H D a u : ℝ} (hX : 1 ≤ X) (b : ℝ) (hH : H = X ^ a)
    (hD : 0 < D) (hDb : D ≤ X ^ b)
    (he : -(1 / 8) + a * (1 / 8) + b * (11 / 8) ≤ a - u) :
    D ^ (7 / 8 : ℝ) * ((H / D ^ 2) / (120 * X / (729 * D ^ 6))) ^ (1 / 8 : ℝ)
      ≤ (7 : ℝ) ^ (1 / 8 : ℝ) * (X ^ a / X ^ u) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hHpos : 0 < H := by rw [hH]; positivity
  apply budget_combine hX (by positivity)
  rotate_left
  · exact he
  -- bound δ/Λ ≤ 7 H D^4 / X
  have hratio : (H / D ^ 2) / (120 * X / (729 * D ^ 6)) = 729 * H * D ^ 4 / (120 * X) := by
    field_simp
  have hle : (H / D ^ 2) / (120 * X / (729 * D ^ 6)) ≤ 7 * H * D ^ 4 / X := by
    rw [hratio]
    rw [div_le_div_iff₀ (by positivity) hXpos]
    have hpos : (0 : ℝ) ≤ H * D ^ 4 * X := by positivity
    nlinarith [hpos]
  have hnn : (0 : ℝ) ≤ (H / D ^ 2) / (120 * X / (729 * D ^ 6)) := by positivity
  -- exact identity for the upper-bounding expression
  have hid : D ^ (7 / 8 : ℝ) * (7 * H * D ^ 4 / X) ^ (1 / 8 : ℝ)
      = 7 ^ (1 / 8 : ℝ) * H ^ (1 / 8 : ℝ) * D ^ (11 / 8 : ℝ) * X ^ (-(1 / 8) : ℝ) := by
    rw [div_rpow (by positivity) hXpos.le, mul_rpow (by positivity) (by positivity),
        mul_rpow (by norm_num) hHpos.le]
    have hd4 : (D ^ 4 : ℝ) ^ (1 / 8 : ℝ) = D ^ (1 / 2 : ℝ) := by
      rw [← rpow_natCast D 4, ← rpow_mul hD.le]; norm_num
    rw [hd4, rpow_neg hXpos.le]
    rw [show (11 / 8 : ℝ) = 7 / 8 + 1 / 2 by norm_num, rpow_add hD]
    rw [div_eq_mul_inv]; ring
  calc D ^ (7 / 8 : ℝ) * ((H / D ^ 2) / (120 * X / (729 * D ^ 6))) ^ (1 / 8 : ℝ)
      ≤ D ^ (7 / 8 : ℝ) * (7 * H * D ^ 4 / X) ^ (1 / 8 : ℝ) := by
        gcongr
    _ = 7 ^ (1 / 8 : ℝ) * H ^ (1 / 8 : ℝ) * D ^ (11 / 8 : ℝ) * X ^ (-(1 / 8) : ℝ) := hid
    _ = 7 ^ (1 / 8 : ℝ) * (X ^ a) ^ (1 / 8 : ℝ) * D ^ (11 / 8 : ℝ) * X ^ (-(1 / 8) : ℝ) := by
        rw [hH]
    _ ≤ 7 ^ (1 / 8 : ℝ) * (X ^ a) ^ (1 / 8 : ℝ) * (X ^ b) ^ (11 / 8 : ℝ) * X ^ (-(1 / 8) : ℝ) := by
        gcongr
    _ = 7 ^ (1 / 8 : ℝ) * X ^ (-(1 / 8) + a * (1 / 8 : ℝ) + b * (11 / 8 : ℝ)) := by
        rw [← rpow_mul hXpos.le, ← rpow_mul hXpos.le]
        rw [show 7 ^ (1 / 8 : ℝ) * X ^ (a * (1 / 8 : ℝ)) * X ^ (b * (11 / 8 : ℝ)) * X ^ (-(1 / 8) : ℝ)
              = 7 ^ (1 / 8 : ℝ) * (X ^ (-(1/8):ℝ) * X ^ (a * (1 / 8 : ℝ)) * X ^ (b * (11 / 8 : ℝ))) by ring]
        rw [← rpow_add hXpos, ← rpow_add hXpos]

/-- Term 4: `Λ^{1/15}·D ≤ X^{1/15 + 3b/5}`. -/
theorem term4_bound {X D a u : ℝ} (hX : 1 ≤ X) (b : ℝ) (hD : 0 < D)
    (hDb : D ≤ X ^ b)
    (he : (1 / 15 : ℝ) + b * (3 / 5) ≤ a - u) :
    (120 * X / (729 * D ^ 6)) ^ (1 / 15 : ℝ) * D ≤ (1 : ℝ) * (X ^ a / X ^ u) := by
  have hXpos : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  apply budget_combine hX (by norm_num)
  rotate_left
  · exact he
  rw [one_mul]
  -- Λ ≤ X/D^6
  have hΛle : 120 * X / (729 * D ^ 6) ≤ X / D ^ 6 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hXpos, pow_pos hD 6]
  have hΛnn : (0 : ℝ) ≤ 120 * X / (729 * D ^ 6) := by positivity
  -- (X/D^6)^{1/15} = X^{1/15}·D^{-2/5}
  have hid : (X / D ^ 6) ^ (1 / 15 : ℝ) * D = X ^ (1 / 15 : ℝ) * D ^ (3 / 5 : ℝ) := by
    rw [div_rpow hXpos.le (by positivity)]
    have hd6 : (D ^ 6 : ℝ) ^ (1 / 15 : ℝ) = D ^ (2 / 5 : ℝ) := by
      rw [← rpow_natCast D 6, ← rpow_mul hD.le]; norm_num
    have hd35 : (D ^ (2 / 5 : ℝ))⁻¹ * D = D ^ (3 / 5 : ℝ) := by
      rw [← rpow_neg hD.le]; nth_rewrite 2 [← rpow_one D]; rw [← rpow_add hD]; norm_num
    rw [hd6, div_eq_mul_inv, mul_assoc, hd35]
  calc (120 * X / (729 * D ^ 6)) ^ (1 / 15 : ℝ) * D
      ≤ (X / D ^ 6) ^ (1 / 15 : ℝ) * D := by
        gcongr
    _ = X ^ (1 / 15 : ℝ) * D ^ (3 / 5 : ℝ) := hid
    _ ≤ X ^ (1 / 15 : ℝ) * (X ^ b) ^ (3 / 5 : ℝ) := by
        gcongr
    _ = X ^ ((1 / 15 : ℝ) + b * (3 / 5 : ℝ)) := by
        rw [← rpow_mul hXpos.le, ← rpow_add hXpos]

end Squarefree.ShortDeltaAux
