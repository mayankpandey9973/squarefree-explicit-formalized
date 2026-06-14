import Squarefree.Lower.Step3Qbound
import Squarefree.Lower.Step3Witness

/-!
# §5 Step-3 per-`r` `|Qval|` bound from `dStar` witness data (writeup 808–816, 870–878)

`Qval_abs_le_from_witness` is the `Qval`-flavoured analogue of `phif_distInt_from_witness`:
given the three `D`-scale witnesses `dStar r, dStar (r+ℓ₁), dStar (r+ℓ₂)` (the `Ra_step3_count`
shape) together with `|v(r)| ≤ V₊`, it discharges the abstract hypotheses of `Qval_abs_le`
and produces the writeup's two-term envelope

```
|Qval P a dStar ℓ₁ ℓ₂ r|
  ≤ 10³⁰·ℓ₁·(H·G·Ω/Δ³)·V₊  +  10³⁰·(G²·U¹⁵/Ω⁵).
```

It derives `Qval_abs_le`'s hypotheses — closeness (`dtilde_close`×3), the discrete slope
(`bzero_le`×2), the Taylor windows (`step1_window_bound`×2), and the defect bound
(`v_defect_le`) — from the witness data, exactly as `phif_distInt_from_witness` does, and
establishes the `Fab`-form relation `h𝒬` from the definition of `Qval`.
-/

open Squarefree.Counting

namespace Squarefree

variable {P : Globals} {S : Scale P}

/-- **§5 Step-3 per-`r` `|Qval|` bound from `dStar` witnesses.** -/
theorem Qval_abs_le_from_witness {a : ℤ} {ℓ₁ ℓ₂ r : ℕ} {dStar : ℕ → ℤ} {Vplus : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ (a : ℝ)) (ha_hi : (a : ℝ) ≤ 11 * S.A)
    (hℓ1 : 0 < ℓ₁) (hℓ12 : ℓ₁ < ℓ₂) (hℓ2W : ((ℓ₂ : ℤ) : ℝ) ≤ 130 * P.Wval)
    (hr_lo : (1/72) * S.R ≤ (r : ℝ)) (hr1_hi : (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) ≤ 16 * S.R)
    (hr2_hi : (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) ≤ 16 * S.R)
    (hdwin : S.D ≤ (dStar r : ℝ) ∧ (dStar r : ℝ) ≤ 2 * S.D)
    (hd1win : S.D ≤ (dStar (r + ℓ₁) : ℝ) ∧ (dStar (r + ℓ₁) : ℝ) ≤ 2 * S.D)
    (hd2win : S.D ≤ (dStar (r + ℓ₂) : ℝ) ∧ (dStar (r + ℓ₂) : ℝ) ≤ 2 * S.D)
    (hRd  : |Rfun P.X (a : ℝ) (dStar r : ℝ) - (r : ℝ)| ≤ 14 * P.H / S.D)
    (hRd1 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₁) : ℝ) - ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ))|
        ≤ 14 * P.H / S.D)
    (hRd2 : |Rfun P.X (a : ℝ) (dStar (r + ℓ₂) : ℝ) - ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ))|
        ≤ 14 * P.H / S.D)
    (hd1ned : (dStar (r + ℓ₁) : ℝ) ≠ (dStar r : ℝ))
    (hd2ned : (dStar (r + ℓ₂) : ℝ) ≠ (dStar r : ℝ))
    (hVplus : |((dStar (r + ℓ₂) : ℝ) - (dStar r : ℝ))
        - ((ℓ₂ : ℤ) : ℝ) / ((ℓ₁ : ℤ) : ℝ) * ((dStar (r + ℓ₁) : ℝ) - (dStar r : ℝ))| ≤ Vplus)
    (hVplus_nn : 0 ≤ Vplus)
    (h1 : P.G * P.U ^ 10 ≤ P.H / S.Δ ^ 2) (hband : 1 ≤ P.G * P.U ^ 3 * S.Ω ^ 4)
    (hG1 : 1 ≤ P.G) (hU1 : 1 ≤ P.U) (hΔ1 : 1 ≤ S.Δ) (hH1 : 1 ≤ P.H)
    (hΩU : S.Ω ≤ P.U) (hUbig : (10:ℝ) ^ 33 ≤ P.U)
    (hΔreg : P.G ^ 2 * P.U ^ 5 ≤ S.Δ) :
    |Qval P a dStar ℓ₁ ℓ₂ r|
      ≤ 10 ^ 34 * ((ℓ₁ : ℤ) : ℝ) * (P.H * P.G * S.Ω / S.Δ ^ 3) * Vplus
        + 10 ^ 34 * (P.G ^ 2 * P.U ^ 15 / S.Ω ^ 5) := by
  -- ===== SETUP : abbreviations for the three integer witnesses, casts =====
  set d : ℤ := dStar r with hd_def
  set d₁ : ℤ := dStar (r + ℓ₁) with hd1_def
  set d₂ : ℤ := dStar (r + ℓ₂) with hd2_def
  have hℓ1Z : (0 : ℤ) < (ℓ₁ : ℤ) := by exact_mod_cast hℓ1
  have hℓ12Z : (ℓ₁ : ℤ) < (ℓ₂ : ℤ) := by exact_mod_cast hℓ12
  have hℓ1_loZ : (1 : ℤ) ≤ (ℓ₁ : ℤ) := hℓ1Z
  have ha0R : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hℓ1R : (0 : ℝ) < ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1Z
  have hℓ12R : ((ℓ₁ : ℤ) : ℝ) < ((ℓ₂ : ℤ) : ℝ) := by exact_mod_cast hℓ12Z
  have hℓ2R : (0 : ℝ) < ((ℓ₂ : ℤ) : ℝ) := lt_trans hℓ1R hℓ12R
  have hℓ1_loR : (1 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := by exact_mod_cast hℓ1_loZ
  have hℓ2_lo : (1 : ℤ) ≤ (ℓ₂ : ℤ) := le_of_lt (lt_of_le_of_lt hℓ1_loZ hℓ12Z)
  have hℓ1nn : (0 : ℝ) ≤ ((ℓ₁ : ℤ) : ℝ) := le_of_lt hℓ1R
  have hℓ2nn : (0 : ℝ) ≤ ((ℓ₂ : ℤ) : ℝ) := le_of_lt hℓ2R
  have hℓ1W : ((ℓ₁ : ℤ) : ℝ) ≤ 130 * P.Wval := le_trans (le_of_lt hℓ12R) hℓ2W
  have hr_hi16 : (r : ℝ) ≤ 16 * S.R := le_trans (by linarith) hr1_hi
  have hr1_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₁ : ℤ) : ℝ) := by linarith
  have hr2_lo : (1/72) * S.R ≤ (r : ℝ) + ((ℓ₂ : ℤ) : ℝ) := by linarith
  -- ===== STEP 1 : closeness ×3 via dtilde_close =====
  have hd_close : |(d : ℝ) - dtilde P.X (r : ℝ) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr_lo hr_hi16 hdwin.1 hdwin.2 hRd
  have hd1_close : |(d₁ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₁ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr1_lo hr1_hi hd1win.1 hd1win.2 hRd1
  have hd2_close : |(d₂ : ℝ) - dtilde P.X ((r : ℝ) + ((ℓ₂ : ℤ) : ℝ)) (a : ℝ)|
      ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) :=
    dtilde_close hAD ha0 ha_lo ha_hi hr2_lo hr2_hi hd2win.1 hd2win.2 hRd2
  -- ===== STEP 2 : b₀ / b₀₂ bounds via bzero_le =====
  set b₀ : ℝ := ((d₁ : ℝ) - (d : ℝ)) / ((ℓ₁ : ℤ) : ℝ) with hb₀_def
  set v : ℝ := ((d₂ : ℝ) - (d : ℝ)) - ((ℓ₂ : ℤ) : ℝ) * b₀ with hv_def
  have hb0 : |b₀| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := (r : ℝ)) (ℓ := ((ℓ₁ : ℤ) : ℝ))
      (d := (d : ℝ)) (dℓ := (d₁ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ1R hℓ1_loR hr_lo hr1_hi hd_close hd1_close hG1 hΔ1
  have hb02 : |((d₂ : ℝ) - (d : ℝ)) / ((ℓ₂ : ℤ) : ℝ)| ≤ 3000000000000 * S.B :=
    bzero_le (P := P) (S := S) (a := (a : ℝ)) (r := (r : ℝ)) (ℓ := ((ℓ₂ : ℤ) : ℝ))
      (d := (d : ℝ)) (dℓ := (d₂ : ℝ))
      hAD ha0R ha_lo ha_hi hℓ2R (by exact_mod_cast hℓ2_lo) hr_lo hr2_hi
      hd_close hd2_close hG1 hΔ1
  -- ===== STEP 3 : U * W ≤ R =====
  have hRUW : P.U * P.Wval ≤ S.R := U_mul_W_le_R (S := S) h1 hband hΩU hΔ1 hU1
  -- ===== STEP 4 : Taylor windows via step1_window_bound =====
  have hwin1 : 4 * ((a : ℝ) + ((ℓ₁ : ℤ) : ℝ) * |b₀|) ≤ (d : ℝ) :=
    step1_window_bound (a := a) (ℓ₂ := (ℓ₁ : ℤ)) (b₀ := b₀) (dd := (d : ℝ))
      ha_hi hℓ1W hℓ1nn hb0 hdwin.1 hRUW hΩU hΔ1 hU1 hUbig
  have hwin2' : 4 * ((a : ℝ) + ((ℓ₂ : ℤ) : ℝ) * |((d₂ : ℝ) - (d : ℝ)) / ((ℓ₂ : ℤ) : ℝ)|)
      ≤ (d : ℝ) :=
    step1_window_bound (a := a) (ℓ₂ := (ℓ₂ : ℤ)) (b₀ := ((d₂ : ℝ) - (d : ℝ)) / ((ℓ₂ : ℤ) : ℝ))
      (dd := (d : ℝ)) ha_hi hℓ2W hℓ2nn hb02 hdwin.1 hRUW hΩU hΔ1 hU1 hUbig
  -- ===== STEP 5 : definitional pinning =====
  have hb0def : ((ℓ₁ : ℤ) : ℝ) * b₀ = (d₁ : ℝ) - (d : ℝ) := by
    rw [hb₀_def]; field_simp
  have hvdef : ((ℓ₂ : ℤ) : ℝ) * b₀ + v = (d₂ : ℝ) - (d : ℝ) := by
    rw [hv_def]; ring
  -- massage hwin2' into the shape Qval_abs_le wants
  have hwin2 : 4 * ((a : ℝ) + |((ℓ₂ : ℤ) : ℝ) * b₀ + v|) ≤ (d : ℝ) := by
    have heq : |((ℓ₂ : ℤ) : ℝ) * b₀ + v| = ((ℓ₂ : ℤ) : ℝ) * |((d₂ : ℝ) - (d : ℝ)) / ((ℓ₂ : ℤ) : ℝ)| := by
      rw [hvdef, abs_div, abs_of_pos hℓ2R]
      field_simp
    rw [heq]; exact hwin2'
  -- ===== STEP 6 : v bound via v_defect_le =====
  have hvd := v_defect_le (P := P) (S := S) (a := a) (r := (r : ℝ))
    (ℓ₁ := (ℓ₁ : ℤ)) (ℓ₂ := (ℓ₂ : ℤ)) (d := d) (d₁ := d₁) (d₂ := d₂)
    hAD ha0 ha_lo ha_hi hℓ1Z hℓ1_loZ hℓ12Z hℓ2W hr_lo hr2_hi
    hd_close hd1_close hd2_close h1 hband hG1 hU1 hΔ1 hΩU hUbig
  have hv_shape : v = ((d₂ : ℝ) - (d : ℝ))
      - (((ℓ₂ : ℤ) : ℝ) / ((ℓ₁ : ℤ) : ℝ)) * ((d₁ : ℝ) - (d : ℝ)) := by
    rw [hv_def, hb₀_def]; ring
  have hv : |v| ≤ 10 ^ 20 * (S.Δ * P.U ^ 5 / S.Ω ^ 3) := by
    rw [hv_shape]
    refine le_trans hvd ?_
    have hnn : (0 : ℝ) ≤ S.Δ * P.U ^ 5 / S.Ω ^ 3 := by
      have := S.Δ_pos; have := P.U_pos; have := S.Ω_pos; positivity
    gcongr
    norm_num
  -- ===== STEP 6b : the `Vplus` hypothesis matches `v` =====
  have hVplus' : |v| ≤ Vplus := by rw [hv_shape]; exact hVplus
  -- ===== STEP 7 : the `Fab`-form relation `h𝒬` for `Qval` =====
  have h𝒬 : Qval P a dStar ℓ₁ ℓ₂ r
      = ((ℓ₁ : ℤ) : ℝ) * Fab P.X (a : ℝ) (((ℓ₂ : ℤ) : ℝ) * b₀ + v) (d : ℝ)
        - ((ℓ₂ : ℤ) : ℝ) * Fab P.X (a : ℝ) (((ℓ₁ : ℤ) : ℝ) * b₀) (d : ℝ) := by
    rw [hvdef, hb0def]
    simp only [Qval, Fab, ← hd_def, ← hd1_def, ← hd2_def]
    have e2 : (d : ℝ) + ((d₂ : ℝ) - (d : ℝ)) = (d₂ : ℝ) := by ring
    have e1 : (d : ℝ) + ((d₁ : ℝ) - (d : ℝ)) = (d₁ : ℝ) := by ring
    rw [e2, e1]; push_cast; ring
  -- ===== STEP 8 : finish via Qval_abs_le =====
  exact Qval_abs_le (P := P) (S := S) (a := a) (r := (r : ℝ))
    (ℓ₁ := (ℓ₁ : ℤ)) (ℓ₂ := (ℓ₂ : ℤ)) (d := d) (d₁ := d₁) (d₂ := d₂)
    (b₀ := b₀) (v := v) (Vplus := Vplus)
    hAD ha0 ha_lo ha_hi hℓ1Z hℓ12Z hℓ2W hr_lo hr_hi16 hdwin
    hb0def hvdef hb0 hv hVplus' hVplus_nn hd1ned hd2ned hwin2 hwin1
    (𝒬 := Qval P a dStar ℓ₁ ℓ₂ r) h𝒬
    h1 hband hG1 hU1 hΔ1 hH1 hΩU hUbig hΔreg

end Squarefree
