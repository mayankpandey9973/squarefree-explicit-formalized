import Squarefree.Bracket.Sec7Defs
import Squarefree.Bracket.Sec7BoxSums
import Squarefree.Opt.OnStripAux
import Mathlib

/-!
# §7 harvests (plan nodes N15, N22)

The two box-sum harvests feeding the Prop 7.1 contradiction (N23): zero top-carry
(md 1770–1825, N15) and nonzero top-carry (md 1942–74, N22). Each takes the per-triple
count bound delivered by its branch (N13 resp. N19+N20, inline with the fiber count (7.2)
and the tolerance bound (7.6)), sums it over `box W` (N14 resp. N21), and discharges every
resulting `W`-power term against an envelope entry (per-entry root-taking: TRAP-4, sympy
MANDATORY at Phase 2), yielding the total `≤ (R/W)/sec7_harvM` that contradicts the
averaged-cube lower bound (N5).

## Constant ledger (ARB-1/ARB-2 pins; tools/sec7_ledger.py)
* `sec7_cTriple = 10⁵⁶` (ARB-2, A6/A4) — the per-triple input constant; chain
  `cFib·cN13·2^{13/4}·11 = 10¹⁰·10⁴³·2^{13/4}·11 ≈ 10^{55.02}` (A4: the AM-6 window
  factor is the per-dyadic `2^{13/4}`, NOT `72^{13/4}` — the global 72-losses already
  sit in `cN13`'s floor).  Ceiling = the envelope margin, met per-entry by the ARB-2
  `sec7_envC2 = 10³⁰⁰` split on `n4–n7` (the four exact ¹⁄₄-power fits of
  `18·cTriple·harvM·cBox = 1.8·10⁶⁴`; all other fits sit at `Σλ ≥ 1/2` on `envC`).
* `sec7_harvM = 10³` — the harvest output margin: N23 needs the N5 cube constant
  `> 1/sec7_harvM`.  (Post-AM-4 the residual entries `res1–res4` are `sec7_envC`-form,
  so they DO carry the `≪`-slack; the old no-slack flag is stale.)
-/

open Classical Finset

namespace Squarefree

/-- Per-triple input constant for the harvests (ledger; ARB-2, A6:
`cFib·cN13·2^{13/4}·11 ≈ 10^{55.02} ≤ 10⁵⁶`). -/
noncomputable def sec7_cTriple : ℝ := 10 ^ 58

/-- Harvest output margin (ledger; provisional — N23 needs the N5 constant `> 1/sec7_harvM`). -/
noncomputable def sec7_harvM : ℝ := 10 ^ 3

theorem sec7_cTriple_pos : (0:ℝ) < sec7_cTriple := by norm_num [sec7_cTriple]
theorem sec7_harvM_pos : (0:ℝ) < sec7_harvM := by norm_num [sec7_harvM]

set_option exponentiation.threshold 1000

/-- The per-summand harvest comparison constant: 18 expanded zero-branch summands. -/
private noncomputable def sec7_harvC : ℝ :=
  18 * sec7_cTriple * sec7_cBox * sec7_harvM

private theorem sec7_harvC_pos : (0:ℝ) < sec7_harvC := by
  norm_num [sec7_harvC, sec7_cTriple, sec7_cBox, sec7_harvM]

private theorem sec7_harvC_le_envC : sec7_harvC ≤ sec7_envC := by
  norm_num [sec7_harvC, sec7_cTriple, sec7_cBox, sec7_harvM, sec7_envC]

private theorem sec7_harvC_sq_le_envC : sec7_harvC ^ 2 ≤ sec7_envC := by
  norm_num [sec7_harvC, sec7_cTriple, sec7_cBox, sec7_harvM, sec7_envC]

private theorem sec7_harvC_four_le_envC2 : sec7_harvC ^ 4 ≤ sec7_envC2 := by
  norm_num [sec7_harvC, sec7_cTriple, sec7_cBox, sec7_harvM, sec7_envC2]

private theorem sec7_le_of_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have hsq := sq_le_sq.mp h
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at hsq

private theorem sec7_le_of_fourth {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 4 ≤ b ^ 4) : a ≤ b := by
  apply sec7_le_of_sq ha hb
  apply sec7_le_of_sq (sq_nonneg a) (sq_nonneg b)
  nlinarith only [h]

private theorem sec7_T₁_pos_local {P : Globals} (S : Scale P) : 0 < S.T₁ := by
  have := P.H_pos; have := P.G_pos; have := S.Δ_pos; have := S.Ω_pos
  unfold Scale.T₁ Scale.F
  positivity

private theorem sec7_T₁_div_R_eval {P : Globals} (S : Scale P) :
    S.T₁ / S.R = 1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.T₁ Scale.F Scale.R Scale.x
  field_simp

private theorem sec7_R_sq_eval {P : Globals} (S : Scale P) :
    S.R ^ 2 = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.R Scale.x
  field_simp

private theorem sec7_R_four_eval {P : Globals} (S : Scale P) :
    S.R ^ 4 = P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12 := by
  have hH := P.H_pos; have hG := P.G_pos; have hΔ := S.Δ_pos; have hΩ := S.Ω_pos
  unfold Scale.R Scale.x
  field_simp

private theorem sec7_box_Pbox_pos {W : ℝ} {p : ℕ × ℕ × ℕ} (hp : p ∈ box W) :
    0 < (Pbox p.1 p.2.1 p.2.2 : ℝ) := by
  have hmem :
      (1 ≤ p.1 ∧ p.1 ≤ ⌊W⌋₊) ∧
        (1 ≤ p.2.1 ∧ p.2.1 ≤ ⌊W ^ 2⌋₊) ∧
          1 ≤ p.2.2 ∧ p.2.2 ≤ ⌊W ^ 4⌋₊ := by
    simpa [box] using hp
  simp only [Pbox]
  exact_mod_cast Nat.mul_pos (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hmem.1.1)
    (lt_of_lt_of_le Nat.zero_lt_one hmem.2.1.1))
    (lt_of_lt_of_le Nat.zero_lt_one hmem.2.2.1)

private theorem sec7_box_Sbox_pos {W : ℝ} {p : ℕ × ℕ × ℕ} (hp : p ∈ box W) :
    0 < (Sbox p.1 p.2.1 p.2.2 : ℝ) := by
  have hmem :
      (1 ≤ p.1 ∧ p.1 ≤ ⌊W⌋₊) ∧
        (1 ≤ p.2.1 ∧ p.2.1 ≤ ⌊W ^ 2⌋₊) ∧
          1 ≤ p.2.2 ∧ p.2.2 ≤ ⌊W ^ 4⌋₊ := by
    simpa [box] using hp
  simp only [Sbox]
  exact_mod_cast Nat.add_pos_left
    (Nat.add_pos_left
      (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hmem.1.1)
        (lt_of_lt_of_le Nat.zero_lt_one hmem.2.1.1))
      (p.1 * p.2.2))
    (p.2.1 * p.2.2)

private theorem sec7_Sbox_mul_sqrt_eq {W : ℝ} {p : ℕ × ℕ × ℕ} (hp : p ∈ box W) :
    (Sbox p.1 p.2.1 p.2.2 : ℝ) *
      (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((1:ℝ)/2) =
        (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((3:ℝ)/2) := by
  have hS := sec7_box_Sbox_pos hp
  calc
    (Sbox p.1 p.2.1 p.2.2 : ℝ) *
        (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((1:ℝ)/2)
        = (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ (1:ℝ) *
          (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((1:ℝ)/2) := by
            rw [Real.rpow_one]
    _ = (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((1:ℝ) + (1:ℝ)/2) := by
          rw [Real.rpow_add hS]
    _ = (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((3:ℝ)/2) := by norm_num

private theorem sec7_inv_sqrt_Pbox_eq {W : ℝ} {p : ℕ × ℕ × ℕ} (hp : p ∈ box W) :
    1 / Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ) =
      (Pbox p.1 p.2.1 p.2.2 : ℝ) ^ (-1/2 : ℝ) := by
  have hP := (sec7_box_Pbox_pos hp).le
  rw [Real.sqrt_eq_rpow, show (-1/2 : ℝ) = -(1/2) by norm_num,
    Real.rpow_neg hP, one_div]

private theorem sec7_box_sums_zero_sqrt : ∀ W : ℝ, 1 ≤ W →
    (∑ p ∈ box W, 1 / Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ))
      ≤ sec7_cBox * W ^ (7/2 : ℝ) ∧
    (∑ p ∈ box W, (Sbox p.1 p.2.1 p.2.2 : ℝ) /
        Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ))
      ≤ sec7_cBox * W ^ (19/2 : ℝ) ∧
    (∑ p ∈ box W, Real.sqrt
        ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)))
      ≤ sec7_cBox * W ^ (13/2 : ℝ) ∧
    (∑ p ∈ box W, (Sbox p.1 p.2.1 p.2.2 : ℝ) * Real.sqrt
        ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)))
      ≤ sec7_cBox * W ^ (25/2 : ℝ) := by
  intro W hW
  rcases sec7_box_sums_zero W hW with
    ⟨_, _, _, _, _, hPmh, hSPmh, hSPh, hSSPh, _, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert hPmh using 1
    refine Finset.sum_congr rfl (fun p hp => ?_)
    exact sec7_inv_sqrt_Pbox_eq hp
  · convert hSPmh using 1
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [div_eq_mul_one_div, sec7_inv_sqrt_Pbox_eq hp]
  · convert hSPh using 1
    refine Finset.sum_congr rfl (fun p _hp => ?_)
    rw [Real.sqrt_eq_rpow]
  · convert hSSPh using 1
    refine Finset.sum_congr rfl (fun p _hp => ?_)
    rw [Real.sqrt_eq_rpow]

private theorem sec7_zero_fit_z1 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 8 * (P.G * S.Ω / S.x ^ 2) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL2 : (1 : ℝ) ≤ (1 + Real.log P.X) ^ 2 := by nlinarith only [hlog0]
  have hC :
      sec7_harvC ^ 2 * W ^ 16 ≤ P.H * S.x ^ 5 * S.Ω ^ 4 := by
    calc
      sec7_harvC ^ 2 * W ^ 16
          ≤ sec7_envC * W ^ 16 := by
            exact mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 16)
      _ ≤ sec7_envC * W ^ 16 * (1 + Real.log P.X) ^ 2 := by
            exact le_mul_of_one_le_right
              (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 16)) hL2
      _ ≤ P.H * S.x ^ 5 * S.Ω ^ 4 := Env.n1
  apply sec7_le_of_sq
  · exact mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 8))
      (div_nonneg (mul_nonneg hG.le hΩ.le) (pow_nonneg hx.le 2))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 8 * (P.G * S.Ω / S.x ^ 2)) ^ 2
        = (sec7_harvC ^ 2 * W ^ 16) * (P.G ^ 2 * S.Ω ^ 2 / S.x ^ 4) := by
          ring
    _ ≤ (P.H * S.x ^ 5 * S.Ω ^ 4) * (P.G ^ 2 * S.Ω ^ 2 / S.x ^ 4) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          field_simp [hx.ne']

private theorem sec7_G_ge_one {P : Globals} (hX1 : 1 ≤ P.X) (hg0 : 0 ≤ P.g) :
    1 ≤ P.G := by
  rw [Globals.G]
  exact Real.one_le_rpow hX1 hg0

private theorem sec7_rpow_pow_nat {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) :
    (x ^ a) ^ n = x ^ (a * (n : ℝ)) := by
  rw [← Real.rpow_natCast (x ^ a) n, ← Real.rpow_mul hx]

private theorem sec7_rpow_four_eq_nat {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ)
    (ha : a * (4 : ℝ) = (n : ℝ)) :
    (x ^ a) ^ 4 = x ^ n := by
  rw [sec7_rpow_pow_nat hx a 4]
  rw [show a * ((4 : ℕ) : ℝ) = (n : ℝ) by simpa using ha, Real.rpow_natCast]

private theorem sec7_rpow_five_halves {x : ℝ} (hx : 0 < x) :
    x ^ ((5:ℝ)/2) = x ^ ((1:ℝ)/2) * x ^ 2 := by
  calc
    x ^ ((5:ℝ)/2) = x ^ (((1:ℝ)/2) + (2:ℝ)) := by norm_num
    _ = x ^ ((1:ℝ)/2) * x ^ (2:ℝ) := by rw [Real.rpow_add hx]
    _ = x ^ ((1:ℝ)/2) * x ^ 2 := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

private theorem sec7_R_mono_nat {P : Globals} (S : Scale P) :
    P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 = S.R := by
  rw [OnStripAux.R_mono P S, Real.rpow_one]
  rw [show S.Ω ^ (3:ℝ) = S.Ω ^ 3 by
    rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]]

private theorem sec7_mul_rpow {W : ℝ} (hW : 0 < W) (a b : ℝ)
    (hab : 1 + a = b) : W * W ^ a = W ^ b := by
  calc
    W * W ^ a = W ^ (1:ℝ) * W ^ a := by rw [Real.rpow_one]
    _ = W ^ (1 + a) := by rw [Real.rpow_add hW]
    _ = W ^ b := by rw [hab]

private theorem sec7_sum_weight_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {A B : ℝ} (hA : 0 ≤ A)
    (hsum : (∑ x ∈ s, f x) ≤ sec7_cBox * B) :
    (∑ x ∈ s, sec7_cTriple * (f x * A)) ≤
      sec7_cTriple * sec7_cBox * (B * A) := by
  calc
    (∑ x ∈ s, sec7_cTriple * (f x * A))
        = sec7_cTriple * ((∑ x ∈ s, f x) * A) := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ sec7_cTriple * ((sec7_cBox * B) * A) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hsum hA) sec7_cTriple_pos.le
    _ = sec7_cTriple * sec7_cBox * (B * A) := by ring

private theorem sec7_slice_of_fit {W R T : ℝ} (hW : 0 < W)
    (hfit : sec7_harvC * W * T ≤ R) :
    sec7_cTriple * sec7_cBox * T ≤ R / (18 * (W * sec7_harvM)) := by
  have hden : 0 < 18 * (W * sec7_harvM) :=
    mul_pos (by norm_num) (mul_pos hW sec7_harvM_pos)
  rw [le_div_iff₀ hden]
  calc
    sec7_cTriple * sec7_cBox * T * (18 * (W * sec7_harvM))
        = sec7_harvC * W * T := by
          rw [sec7_harvC]
          ring
    _ ≤ R := hfit

private theorem sec7_root1_fiber_mono {P : Globals} {S : Scale P} :
    (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)) / (P.G * S.Ω ^ 5)
      =
    P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((3:ℝ)/2) * S.Ω ^ ((3:ℝ)/2) := by
  have hG := P.G_pos; have hΩ := S.Ω_pos
  have hGdiv : P.G ^ ((5:ℝ)/2) / P.G = P.G ^ ((3:ℝ)/2) := by
    have hG1 : P.G ^ (1:ℝ) = P.G := Real.rpow_one P.G
    calc
      P.G ^ ((5:ℝ)/2) / P.G = P.G ^ ((5:ℝ)/2) / P.G ^ (1:ℝ) := by rw [hG1]
      _ = P.G ^ (((5:ℝ)/2) - 1) := by rw [← Real.rpow_sub hG]
      _ = P.G ^ ((3:ℝ)/2) := by norm_num
  have hΩ5 : S.Ω ^ 5 = S.Ω ^ (5:ℝ) := by
    rw [show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hΩdiv : S.Ω ^ ((13:ℝ)/2) / S.Ω ^ 5 = S.Ω ^ ((3:ℝ)/2) := by
    rw [hΩ5, ← Real.rpow_sub hΩ]
    norm_num
  calc
    (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)) / (P.G * S.Ω ^ 5)
        =
      (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4)) *
        (P.G ^ ((5:ℝ)/2) / P.G) *
        (S.Ω ^ ((13:ℝ)/2) / S.Ω ^ 5) := by
          field_simp [hG.ne', hΩ.ne']
    _ = P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((3:ℝ)/2) * S.Ω ^ ((3:ℝ)/2) := by
          rw [hGdiv, hΩdiv]

private theorem sec7_root2_fiber_mono {P : Globals} {S : Scale P} :
    (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4) /
        (P.G * S.Ω ^ 5)
      = P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) / S.Ω := by
  have hG := P.G_pos; have hΩ := S.Ω_pos
  field_simp [hG.ne', hΩ.ne']

private theorem sec7_zero_fit_res1 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 8 * (S.Ω ^ 2 / P.H) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL2 : (1 : ℝ) ≤ (1 + Real.log P.X) ^ 2 := by nlinarith only [hlog0]
  have hC : sec7_harvC ^ 2 * W ^ 16 ≤ P.H ^ 3 * S.x * P.G ^ 2 * S.Ω ^ 2 := by
    calc
      sec7_harvC ^ 2 * W ^ 16 ≤ sec7_envC * W ^ 16 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 16)
      _ ≤ sec7_envC * W ^ 16 * (1 + Real.log P.X) ^ 2 := by
        exact le_mul_of_one_le_right
          (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 16)) hL2
      _ ≤ P.H ^ 3 * S.x * P.G ^ 2 * S.Ω ^ 2 := Env.res1
  apply sec7_le_of_sq
  · exact mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 8))
      (div_nonneg (pow_nonneg hΩ.le 2) hH.le)
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 8 * (S.Ω ^ 2 / P.H)) ^ 2
        = (sec7_harvC ^ 2 * W ^ 16) * (S.Ω ^ 4 / P.H ^ 2) := by ring
    _ ≤ (P.H ^ 3 * S.x * P.G ^ 2 * S.Ω ^ 2) * (S.Ω ^ 4 / P.H ^ 2) := by
        exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
        field_simp [hH.ne']

private theorem sec7_zero_fit_n2_base {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X)
    (hG1 : 1 ≤ P.G) :
    sec7_harvC * W ^ 14 * (1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL2 : (1 : ℝ) ≤ (1 + Real.log P.X) ^ 2 := by nlinarith only [hlog0]
  have hC : sec7_harvC ^ 2 * W ^ 28 ≤ P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14 := by
    calc
      sec7_harvC ^ 2 * W ^ 28 ≤ sec7_envC * W ^ 28 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 28)
      _ ≤ sec7_envC * W ^ 28 * (1 + Real.log P.X) ^ 2 := by
        exact le_mul_of_one_le_right
          (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 28)) hL2
      _ ≤ P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14 := Env.n2
  apply sec7_le_of_sq
  · exact mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 14))
      (one_div_nonneg.mpr
        (mul_nonneg (mul_nonneg (pow_nonneg hx.le 2) (pow_nonneg hG.le 2))
          (pow_nonneg hΩ.le 4)))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 14 * (1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4))) ^ 2
        = (sec7_harvC ^ 2 * W ^ 28) / (S.x ^ 4 * P.G ^ 4 * S.Ω ^ 8) := by
          field_simp [hx.ne', hG.ne', hΩ.ne']
    _ ≤ (P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14) /
          (S.x ^ 4 * P.G ^ 4 * S.Ω ^ 8) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * S.Ω ^ 6 / P.G ^ 2 := by
          field_simp [hx.ne', hG.ne', hΩ.ne']
    _ ≤ P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          have hG2pos : 0 < P.G ^ 2 := pow_pos hG 2
          have hG2 : (1 : ℝ) ≤ P.G ^ 2 := by nlinarith only [hG1]
          have hdiv : 1 / P.G ^ 2 ≤ P.G ^ 2 := by
            rw [one_div]
            exact (inv_le_one_of_one_le₀ hG2).trans hG2
          have hA0 : 0 ≤ P.H * S.x * S.Ω ^ 6 := by positivity
          calc
            P.H * S.x * S.Ω ^ 6 / P.G ^ 2
                = (P.H * S.x * S.Ω ^ 6) * (1 / P.G ^ 2) := by ring
            _ ≤ (P.H * S.x * S.Ω ^ 6) * (P.G ^ 2) :=
                mul_le_mul_of_nonneg_left hdiv hA0
            _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by ring

private theorem sec7_zero_fit_n2_fiber {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * (1 / (S.x ^ 2 * S.Ω ^ 4)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL2 : (1 : ℝ) ≤ (1 + Real.log P.X) ^ 2 := by nlinarith only [hlog0]
  have hC : sec7_harvC ^ 2 * W ^ 28 ≤ P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14 := by
    calc
      sec7_harvC ^ 2 * W ^ 28 ≤ sec7_envC * W ^ 28 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 28)
      _ ≤ sec7_envC * W ^ 28 * (1 + Real.log P.X) ^ 2 := by
        exact le_mul_of_one_le_right
          (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 28)) hL2
      _ ≤ P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14 := Env.n2
  apply sec7_le_of_sq
  · exact mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 14))
      (one_div_nonneg.mpr
        (mul_nonneg (pow_nonneg hx.le 2) (pow_nonneg hΩ.le 4)))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 14 * (1 / (S.x ^ 2 * S.Ω ^ 4))) ^ 2
        = (sec7_harvC ^ 2 * W ^ 28) / (S.x ^ 4 * S.Ω ^ 8) := by
          field_simp [hx.ne', hΩ.ne']
    _ ≤ (P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14) / (S.x ^ 4 * S.Ω ^ 8) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          field_simp [hx.ne', hΩ.ne']

private theorem sec7_zero_fit_n3 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 20 * (1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL2 : (1 : ℝ) ≤ (1 + Real.log P.X) ^ 2 := by nlinarith only [hlog0]
  have hC : sec7_harvC ^ 2 * W ^ 40 ≤ P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24 := by
    calc
      sec7_harvC ^ 2 * W ^ 40 ≤ sec7_envC * W ^ 40 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 40)
      _ ≤ sec7_envC * W ^ 40 * (1 + Real.log P.X) ^ 2 := by
        exact le_mul_of_one_le_right
          (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 40)) hL2
      _ ≤ P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24 := Env.n3
  apply sec7_le_of_sq
  · exact mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 20))
      (one_div_nonneg.mpr
        (mul_nonneg (mul_nonneg (pow_nonneg hx.le 2) (pow_nonneg hG.le 3))
          (pow_nonneg hΩ.le 9)))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 20 * (1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9))) ^ 2
        = (sec7_harvC ^ 2 * W ^ 40) / (S.x ^ 4 * P.G ^ 6 * S.Ω ^ 18) := by
          field_simp [hx.ne', hG.ne', hΩ.ne']
    _ ≤ (P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24) /
          (S.x ^ 4 * P.G ^ 6 * S.Ω ^ 18) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          field_simp [hx.ne', hG.ne', hΩ.ne']

private theorem sec7_zero_fit_n8 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ 15 * (1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hC : sec7_harvC ^ 2 * W ^ 30 ≤ P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24 := by
    calc
      sec7_harvC ^ 2 * W ^ 30 ≤ sec7_envC * W ^ 30 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 30)
      _ ≤ P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24 := Env.n8
  apply sec7_le_of_sq
  · exact mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 15))
      (one_div_nonneg.mpr
        (mul_nonneg (mul_nonneg (pow_nonneg hx.le 2) (pow_nonneg hG.le 3))
          (pow_nonneg hΩ.le 9)))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 15 * (1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9))) ^ 2
        = (sec7_harvC ^ 2 * W ^ 30) / (S.x ^ 4 * P.G ^ 6 * S.Ω ^ 18) := by
          field_simp [hx.ne', hG.ne', hΩ.ne']
    _ ≤ (P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24) /
          (S.x ^ 4 * P.G ^ 6 * S.Ω ^ 18) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          field_simp [hx.ne', hG.ne', hΩ.ne']

private theorem sec7_zero_fit_n9 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ 21 * (1 / (S.x ^ 2 * P.G ^ 4 * S.Ω ^ 14)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hC : sec7_harvC ^ 2 * W ^ 42 ≤ P.H * S.x ^ 5 * P.G ^ 10 * S.Ω ^ 34 := by
    calc
      sec7_harvC ^ 2 * W ^ 42 ≤ sec7_envC * W ^ 42 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 42)
      _ ≤ P.H * S.x ^ 5 * P.G ^ 10 * S.Ω ^ 34 := Env.n9
  apply sec7_le_of_sq
  · exact mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 21))
      (one_div_nonneg.mpr
        (mul_nonneg (mul_nonneg (pow_nonneg hx.le 2) (pow_nonneg hG.le 4))
          (pow_nonneg hΩ.le 14)))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 21 * (1 / (S.x ^ 2 * P.G ^ 4 * S.Ω ^ 14))) ^ 2
        = (sec7_harvC ^ 2 * W ^ 42) / (S.x ^ 4 * P.G ^ 8 * S.Ω ^ 28) := by
          field_simp [hx.ne', hG.ne', hΩ.ne']
    _ ≤ (P.H * S.x ^ 5 * P.G ^ 10 * S.Ω ^ 34) /
          (S.x ^ 4 * P.G ^ 8 * S.Ω ^ 28) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          field_simp [hx.ne', hG.ne', hΩ.ne']

private theorem sec7_zero_fit_res2 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * (1 / (P.H * P.G * S.Ω ^ 3)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL2 : (1 : ℝ) ≤ (1 + Real.log P.X) ^ 2 := by nlinarith only [hlog0]
  have hC : sec7_harvC ^ 2 * W ^ 28 ≤ P.H ^ 3 * S.x * P.G ^ 4 * S.Ω ^ 12 := by
    calc
      sec7_harvC ^ 2 * W ^ 28 ≤ sec7_envC * W ^ 28 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 28)
      _ ≤ sec7_envC * W ^ 28 * (1 + Real.log P.X) ^ 2 := by
        exact le_mul_of_one_le_right
          (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 28)) hL2
      _ ≤ P.H ^ 3 * S.x * P.G ^ 4 * S.Ω ^ 12 := Env.res2
  apply sec7_le_of_sq
  · exact mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 14))
      (one_div_nonneg.mpr
        (mul_nonneg (mul_nonneg hH.le hG.le) (pow_nonneg hΩ.le 3)))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 14 * (1 / (P.H * P.G * S.Ω ^ 3))) ^ 2
        = (sec7_harvC ^ 2 * W ^ 28) / (P.H ^ 2 * P.G ^ 2 * S.Ω ^ 6) := by
          field_simp [hH.ne', hG.ne', hΩ.ne']
    _ ≤ (P.H ^ 3 * S.x * P.G ^ 4 * S.Ω ^ 12) /
          (P.H ^ 2 * P.G ^ 2 * S.Ω ^ 6) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          field_simp [hH.ne', hG.ne', hΩ.ne']

private theorem sec7_zero_fit_off1_den {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ 12 * (1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hC : sec7_harvC * W ^ 12 ≤
      P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7 := by
    calc
      sec7_harvC * W ^ 12 ≤ sec7_envC * W ^ 12 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 12)
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7 := Env.off1
  calc
    sec7_harvC * W ^ 12 * (1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4))
        = (sec7_harvC * W ^ 12) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by ring
    _ ≤ (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 3 * S.Ω ^ 7) /
          (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
          rw [sec7_rpow_five_halves hx]
          field_simp [hx.ne', hG.ne', hΩ.ne']
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_zero_fit_off1 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ 12 * (S.T₁ / S.R) ≤ S.R := by
  rw [sec7_T₁_div_R_eval]
  exact sec7_zero_fit_off1_den Env hW

private theorem sec7_zero_fit_off2_den {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ 18 * (1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hC : sec7_harvC * W ^ 18 ≤
      P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 4 * S.Ω ^ 12 := by
    calc
      sec7_harvC * W ^ 18 ≤ sec7_envC * W ^ 18 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 18)
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 4 * S.Ω ^ 12 := Env.off2
  calc
    sec7_harvC * W ^ 18 * (1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9))
        = (sec7_harvC * W ^ 18) / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) := by ring
    _ ≤ (P.H ^ ((1:ℝ)/2) * S.x ^ ((5:ℝ)/2) * P.G ^ 4 * S.Ω ^ 12) /
          (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
          rw [sec7_rpow_five_halves hx]
          field_simp [hx.ne', hG.ne', hΩ.ne']
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_zero_fit_off2 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ 18 * ((S.T₁ / S.R) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hG := P.G_pos; have hΩ := S.Ω_pos
  rw [sec7_T₁_div_R_eval]
  convert sec7_zero_fit_off2_den Env hW using 1
  field_simp [hG.ne', hΩ.ne']

private theorem sec7_zero_fit_tc4 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 8 ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hlog1 : (1 : ℝ) ≤ 1 + Real.log P.X := by linarith only [hlog0]
  calc
    sec7_harvC * W ^ 8 ≤ sec7_envC * W ^ 8 := by
      exact mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 8)
    _ ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
      exact le_mul_of_one_le_right
        (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 8)) hlog1
    _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := Env.tc4
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_zero_fit_tc8 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * (1 / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hG := P.G_pos; have hΩ := S.Ω_pos
  have hlog1 : (1 : ℝ) ≤ 1 + Real.log P.X := by linarith only [hlog0]
  have hC : sec7_harvC * W ^ 14 ≤
      P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := by
    calc
      sec7_harvC * W ^ 14 ≤ sec7_envC * W ^ 14 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 14)
      _ ≤ sec7_envC * W ^ 14 * (1 + Real.log P.X) := by
        exact le_mul_of_one_le_right
          (mul_nonneg sec7_envC_pos.le (pow_nonneg hW0 14)) hlog1
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := Env.tc8
  calc
    sec7_harvC * W ^ 14 * (1 / (P.G * S.Ω ^ 5))
        = (sec7_harvC * W ^ 14) / (P.G * S.Ω ^ 5) := by ring
    _ ≤ (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) /
          (P.G * S.Ω ^ 5) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
          field_simp [hG.ne', hΩ.ne']
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_zero_fit_n4 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ ((9:ℝ)/2) *
      (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hC : sec7_harvC ^ 4 * (W ^ 18 * P.G ^ 6 * S.Ω ^ 14) ≤ P.H * S.x := by
    calc
      sec7_harvC ^ 4 * (W ^ 18 * P.G ^ 6 * S.Ω ^ 14)
          ≤ sec7_envC2 * (W ^ 18 * P.G ^ 6 * S.Ω ^ 14) := by
            exact mul_le_mul_of_nonneg_right sec7_harvC_four_le_envC2 (by positivity)
      _ ≤ P.H * S.x := Env.n4
  apply sec7_le_of_fourth
  · have hHx : 0 ≤ P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) :=
      mul_nonneg (Real.rpow_nonneg hH.le _) (Real.rpow_nonneg hx.le _)
    have hHxG : 0 ≤ P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((5:ℝ)/2) :=
      mul_nonneg hHx (Real.rpow_nonneg hG.le _)
    have hmono : 0 ≤ P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2) :=
      mul_nonneg hHxG (Real.rpow_nonneg hΩ.le _)
    exact mul_nonneg
      (mul_nonneg sec7_harvC_pos.le (Real.rpow_nonneg hW0 _)) hmono
  · exact (sec7_R_pos S).le
  rw [sec7_R_four_eval]
  calc
    (sec7_harvC * W ^ ((9:ℝ)/2) *
      (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2))) ^ 4
        = (sec7_harvC ^ 4 * (W ^ 18 * P.G ^ 6 * S.Ω ^ 14)) *
            (P.H * S.x * P.G ^ 4 * S.Ω ^ 12) := by
          repeat rw [mul_pow]
          rw [sec7_rpow_four_eq_nat hW0 ((9:ℝ)/2) 18 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hH.le ((1:ℝ)/4) 1 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hx.le ((1:ℝ)/4) 1 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hG.le ((5:ℝ)/2) 10 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hΩ.le ((13:ℝ)/2) 26 (by norm_num)]
          ring
    _ ≤ (P.H * S.x) * (P.H * S.x * P.G ^ 4 * S.Ω ^ 12) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12 := by ring

private theorem sec7_zero_fit_n5 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ ((21:ℝ)/2) *
      (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((3:ℝ)/2) * S.Ω ^ ((3:ℝ)/2)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hC : sec7_harvC ^ 4 * (W ^ 42 * P.G ^ 2) ≤ P.H * S.x * S.Ω ^ 6 := by
    calc
      sec7_harvC ^ 4 * (W ^ 42 * P.G ^ 2)
          ≤ sec7_envC2 * (W ^ 42 * P.G ^ 2) := by
            exact mul_le_mul_of_nonneg_right sec7_harvC_four_le_envC2 (by positivity)
      _ ≤ P.H * S.x * S.Ω ^ 6 := Env.n5
  apply sec7_le_of_fourth
  · have hHx : 0 ≤ P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) :=
      mul_nonneg (Real.rpow_nonneg hH.le _) (Real.rpow_nonneg hx.le _)
    have hHxG : 0 ≤ P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((3:ℝ)/2) :=
      mul_nonneg hHx (Real.rpow_nonneg hG.le _)
    have hmono : 0 ≤ P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((3:ℝ)/2) * S.Ω ^ ((3:ℝ)/2) :=
      mul_nonneg hHxG (Real.rpow_nonneg hΩ.le _)
    exact mul_nonneg
      (mul_nonneg sec7_harvC_pos.le (Real.rpow_nonneg hW0 _)) hmono
  · exact (sec7_R_pos S).le
  rw [sec7_R_four_eval]
  calc
    (sec7_harvC * W ^ ((21:ℝ)/2) *
      (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
        P.G ^ ((3:ℝ)/2) * S.Ω ^ ((3:ℝ)/2))) ^ 4
        = (sec7_harvC ^ 4 * (W ^ 42 * P.G ^ 2)) *
            (P.H * S.x * P.G ^ 4 * S.Ω ^ 6) := by
          repeat rw [mul_pow]
          rw [sec7_rpow_four_eq_nat hW0 ((21:ℝ)/2) 42 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hH.le ((1:ℝ)/4) 1 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hx.le ((1:ℝ)/4) 1 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hG.le ((3:ℝ)/2) 6 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hΩ.le ((3:ℝ)/2) 6 (by norm_num)]
          ring
    _ ≤ (P.H * S.x * S.Ω ^ 6) * (P.H * S.x * P.G ^ 4 * S.Ω ^ 6) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12 := by ring

private theorem sec7_zero_fit_n6 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ ((15:ℝ)/2) *
      (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hC : sec7_harvC ^ 4 * (W ^ 30 * S.Ω ^ 4) ≤ P.H * S.x := by
    calc
      sec7_harvC ^ 4 * (W ^ 30 * S.Ω ^ 4)
          ≤ sec7_envC2 * (W ^ 30 * S.Ω ^ 4) := by
            exact mul_le_mul_of_nonneg_right sec7_harvC_four_le_envC2 (by positivity)
      _ ≤ P.H * S.x := Env.n6
  apply sec7_le_of_fourth
  · have hHx : 0 ≤ P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) :=
      mul_nonneg (Real.rpow_nonneg hH.le _) (Real.rpow_nonneg hx.le _)
    have hHxG : 0 ≤ P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G :=
      mul_nonneg hHx hG.le
    have hmono : 0 ≤ P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 :=
      mul_nonneg hHxG (pow_nonneg hΩ.le 4)
    exact mul_nonneg
      (mul_nonneg sec7_harvC_pos.le (Real.rpow_nonneg hW0 _)) hmono
  · exact (sec7_R_pos S).le
  rw [sec7_R_four_eval]
  calc
    (sec7_harvC * W ^ ((15:ℝ)/2) *
      (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4)) ^ 4
        = (sec7_harvC ^ 4 * (W ^ 30 * S.Ω ^ 4)) *
            (P.H * S.x * P.G ^ 4 * S.Ω ^ 12) := by
          repeat rw [mul_pow]
          rw [sec7_rpow_four_eq_nat hW0 ((15:ℝ)/2) 30 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hH.le ((1:ℝ)/4) 1 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hx.le ((1:ℝ)/4) 1 (by norm_num)]
          ring
    _ ≤ (P.H * S.x) * (P.H * S.x * P.G ^ 4 * S.Ω ^ 12) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12 := by ring

private theorem sec7_zero_fit_n7 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ ((27:ℝ)/2) *
      (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) / S.Ω) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hC : sec7_harvC ^ 4 * W ^ 54 ≤ P.H * S.x * P.G ^ 4 * S.Ω ^ 16 := by
    calc
      sec7_harvC ^ 4 * W ^ 54 ≤ sec7_envC2 * W ^ 54 := by
        exact mul_le_mul_of_nonneg_right sec7_harvC_four_le_envC2 (pow_nonneg hW0 54)
      _ ≤ P.H * S.x * P.G ^ 4 * S.Ω ^ 16 := Env.n7
  apply sec7_le_of_fourth
  · exact mul_nonneg
      (mul_nonneg sec7_harvC_pos.le (Real.rpow_nonneg hW0 _))
      (div_nonneg
        (mul_nonneg (Real.rpow_nonneg hH.le _) (Real.rpow_nonneg hx.le _)) hΩ.le)
  · exact (sec7_R_pos S).le
  rw [sec7_R_four_eval]
  calc
    (sec7_harvC * W ^ ((27:ℝ)/2) *
      (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) / S.Ω)) ^ 4
        = (sec7_harvC ^ 4 * W ^ 54) *
            (P.H * S.x / S.Ω ^ 4) := by
          repeat rw [mul_pow]
          rw [div_pow]
          repeat rw [mul_pow]
          rw [sec7_rpow_four_eq_nat hW0 ((27:ℝ)/2) 54 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hH.le ((1:ℝ)/4) 1 (by norm_num)]
          rw [sec7_rpow_four_eq_nat hx.le ((1:ℝ)/4) 1 (by norm_num)]
          field_simp [hΩ.ne']
    _ ≤ (P.H * S.x * P.G ^ 4 * S.Ω ^ 16) * (P.H * S.x / S.Ω ^ 4) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = P.H ^ 2 * S.x ^ 2 * P.G ^ 4 * S.Ω ^ 12 := by
          field_simp [hΩ.ne']

private theorem sec7_zero_fit_z1_fiber_raw {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * ((P.G * S.Ω / S.x ^ 2) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := OnStripAux.x_pos P S
  convert sec7_zero_fit_n2_fiber Env hW hlog0 using 1
  field_simp [hG.ne', hΩ.ne', hx.ne']

private theorem sec7_zero_fit_res2_raw {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * ((S.Ω ^ 2 / P.H) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  convert sec7_zero_fit_res2 Env hW hlog0 using 1
  field_simp [hH.ne', hG.ne', hΩ.ne']

private theorem sec7_zero_fit_n3_raw {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 20 *
      ((1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := OnStripAux.x_pos P S
  convert sec7_zero_fit_n3 Env hW hlog0 using 1
  field_simp [hG.ne', hΩ.ne', hx.ne']

private theorem sec7_zero_fit_n5_raw {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ ((21:ℝ)/2) *
      ((P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
          P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  rw [sec7_root1_fiber_mono]
  exact sec7_zero_fit_n5 Env hW

private theorem sec7_zero_fit_n7_raw {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ ((27:ℝ)/2) *
      ((P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4) /
        (P.G * S.Ω ^ 5)) ≤ S.R := by
  rw [sec7_root2_fiber_mono]
  exact sec7_zero_fit_n7 Env hW

private theorem sec7_zero_fit_off2_den_raw {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ 18 *
      ((1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := OnStripAux.x_pos P S
  convert sec7_zero_fit_off2_den Env hW using 1
  field_simp [hG.ne', hΩ.ne', hx.ne']

private theorem sec7_zero_fit_n9_raw {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) :
    sec7_harvC * W ^ 21 *
      ((1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := OnStripAux.x_pos P S
  convert sec7_zero_fit_n9 Env hW using 1
  field_simp [hG.ne', hΩ.ne', hx.ne']

private theorem sec7_nonzero_tc1_cube_mono {P : Globals} {S : Scale P} :
    (P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G * S.Ω ^ ((7:ℝ)/3)) *
      (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) = S.R := by
  have hH := P.H_pos
  have hx := OnStripAux.x_pos P S
  have hΩ := S.Ω_pos
  calc
    (P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G * S.Ω ^ ((7:ℝ)/3)) *
        (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3))
        =
      (P.H ^ ((1:ℝ)/6) * P.H ^ ((1:ℝ)/3)) *
        (S.x ^ ((5:ℝ)/6) * S.x ^ (-(1:ℝ)/3)) * P.G *
          (S.Ω ^ ((7:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) := by ring
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ (3:ℝ) := by
      rw [← Real.rpow_add hH, ← Real.rpow_add hx, ← Real.rpow_add hΩ]
      norm_num
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
      rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_nonzero_tc5_cube_fiber_mono {P : Globals} {S : Scale P} :
    (P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G ^ 2 * S.Ω ^ ((22:ℝ)/3)) *
      ((P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) /
        (P.G * S.Ω ^ 5)) = S.R := by
  have hH := P.H_pos
  have hG := P.G_pos
  have hx := OnStripAux.x_pos P S
  have hΩ := S.Ω_pos
  calc
    (P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G ^ 2 * S.Ω ^ ((22:ℝ)/3)) *
        ((P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) /
          (P.G * S.Ω ^ 5))
        =
      ((P.H ^ ((1:ℝ)/6) * P.H ^ ((1:ℝ)/3)) *
        (S.x ^ ((5:ℝ)/6) * S.x ^ (-(1:ℝ)/3)) * P.G ^ 2 *
          (S.Ω ^ ((22:ℝ)/3) * S.Ω ^ ((2:ℝ)/3))) / (P.G * S.Ω ^ 5) := by ring
    _ = (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ (8:ℝ)) /
        (P.G * S.Ω ^ 5) := by
      rw [← Real.rpow_add hH, ← Real.rpow_add hx, ← Real.rpow_add hΩ]
      norm_num
    _ = (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) /
        (P.G * S.Ω ^ 5) := by
      rw [show (8:ℝ) = ((8:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
      field_simp [hG.ne', hΩ.ne']
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_nonzero_tc2_main_root_mono {P : Globals} {S : Scale P} :
    (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (-(1:ℝ)/2) *
        S.Ω ^ ((1:ℝ)/2)) *
      (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) = S.R := by
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  calc
    (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (-(1:ℝ)/2) *
        S.Ω ^ ((1:ℝ)/2)) *
        (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2))
        =
      P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) *
        (P.G ^ (-(1:ℝ)/2) * P.G ^ ((3:ℝ)/2)) *
          (S.Ω ^ ((1:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) := by ring
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (1:ℝ) * S.Ω ^ (3:ℝ) := by
      rw [← Real.rpow_add hG, ← Real.rpow_add hΩ]
      norm_num
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
      rw [Real.rpow_one, show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_nonzero_tc6_main_root_fiber_mono {P : Globals} {S : Scale P} :
    (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ ((1:ℝ)/2) *
        S.Ω ^ ((11:ℝ)/2)) *
      ((P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) / (P.G * S.Ω ^ 5)) = S.R := by
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  calc
    (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ ((1:ℝ)/2) *
        S.Ω ^ ((11:ℝ)/2)) *
        ((P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) / (P.G * S.Ω ^ 5))
        =
      (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) *
        (P.G ^ ((1:ℝ)/2) * P.G ^ ((3:ℝ)/2)) *
          (S.Ω ^ ((11:ℝ)/2) * S.Ω ^ ((5:ℝ)/2))) / (P.G * S.Ω ^ 5) := by ring
    _ = (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (2:ℝ) * S.Ω ^ (8:ℝ)) /
        (P.G * S.Ω ^ 5) := by
      rw [← Real.rpow_add hG, ← Real.rpow_add hΩ]
      norm_num
    _ = (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) /
        (P.G * S.Ω ^ 5) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
        show (8:ℝ) = ((8:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
      field_simp [hG.ne', hΩ.ne']
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_nonzero_tc7_fiber_mono {P : Globals} {S : Scale P} :
    (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) *
      (1 / (P.G * S.Ω ^ 5)) = S.R := by
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  calc
    (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) *
        (1 / (P.G * S.Ω ^ 5))
        = (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) /
          (P.G * S.Ω ^ 5) := by ring
    _ = P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := by
      field_simp [hG.ne', hΩ.ne']
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_nonzero_fit_tc1 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 8 * (1 + Real.log P.X) *
      (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hA : 0 ≤ P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3) := by
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg P.H_pos.le _) (Real.rpow_nonneg (OnStripAux.x_pos P S).le _))
      (Real.rpow_nonneg S.Ω_pos.le _)
  have hC : sec7_harvC * W ^ 8 * (1 + Real.log P.X) ≤
      P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G * S.Ω ^ ((7:ℝ)/3) := by
    calc
      sec7_harvC * W ^ 8 * (1 + Real.log P.X)
          ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 8)) hL0
      _ ≤ P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G * S.Ω ^ ((7:ℝ)/3) := Env.tc1
  calc
    sec7_harvC * W ^ 8 * (1 + Real.log P.X) *
        (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3))
        ≤
      (P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G * S.Ω ^ ((7:ℝ)/3)) *
        (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) :=
          mul_le_mul_of_nonneg_right hC hA
    _ = S.R := sec7_nonzero_tc1_cube_mono

private theorem sec7_nonzero_fit_tc5 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
      ((P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) /
        (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hA : 0 ≤ (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) /
      (P.G * S.Ω ^ 5) := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (Real.rpow_nonneg P.H_pos.le _) (Real.rpow_nonneg (OnStripAux.x_pos P S).le _))
        (Real.rpow_nonneg S.Ω_pos.le _))
      (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5))
  have hC : sec7_harvC * W ^ 14 * (1 + Real.log P.X) ≤
      P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G ^ 2 * S.Ω ^ ((22:ℝ)/3) := by
    calc
      sec7_harvC * W ^ 14 * (1 + Real.log P.X)
          ≤ sec7_envC * W ^ 14 * (1 + Real.log P.X) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 14)) hL0
      _ ≤ P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G ^ 2 * S.Ω ^ ((22:ℝ)/3) := Env.tc5
  calc
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
        ((P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) /
          (P.G * S.Ω ^ 5))
        ≤
      (P.H ^ ((1:ℝ)/6) * S.x ^ ((5:ℝ)/6) * P.G ^ 2 * S.Ω ^ ((22:ℝ)/3)) *
        ((P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)) /
          (P.G * S.Ω ^ 5)) := mul_le_mul_of_nonneg_right hC hA
    _ = S.R := sec7_nonzero_tc5_cube_fiber_mono

private theorem sec7_nonzero_fit_n1 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 8 * (1 + Real.log P.X) * (P.G * S.Ω / S.x ^ 2) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hC : sec7_harvC ^ 2 * W ^ 16 * (1 + Real.log P.X) ^ 2 ≤
      P.H * S.x ^ 5 * S.Ω ^ 4 := by
    calc
      sec7_harvC ^ 2 * W ^ 16 * (1 + Real.log P.X) ^ 2
          ≤ sec7_envC * W ^ 16 * (1 + Real.log P.X) ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 16))
              (sq_nonneg _)
      _ ≤ P.H * S.x ^ 5 * S.Ω ^ 4 := Env.n1
  apply sec7_le_of_sq
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 8)) hL0)
      (div_nonneg (mul_nonneg hG.le hΩ.le) (pow_nonneg hx.le 2))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 8 * (1 + Real.log P.X) * (P.G * S.Ω / S.x ^ 2)) ^ 2
        = (sec7_harvC ^ 2 * W ^ 16 * (1 + Real.log P.X) ^ 2) *
          (P.G ^ 2 * S.Ω ^ 2 / S.x ^ 4) := by ring
    _ ≤ (P.H * S.x ^ 5 * S.Ω ^ 4) * (P.G ^ 2 * S.Ω ^ 2 / S.x ^ 4) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          field_simp [hx.ne']

private theorem sec7_nonzero_fit_n2_fiber_z1 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
      ((P.G * S.Ω / S.x ^ 2) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := OnStripAux.x_pos P S
  convert (show sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
      (1 / (S.x ^ 2 * S.Ω ^ 4)) ≤ S.R from by
    have hW0 : 0 ≤ W := le_trans zero_le_one hW
    have hH := P.H_pos
    have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
    have hC : sec7_harvC ^ 2 * W ^ 28 * (1 + Real.log P.X) ^ 2 ≤
        P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14 := by
      calc
        sec7_harvC ^ 2 * W ^ 28 * (1 + Real.log P.X) ^ 2
            ≤ sec7_envC * W ^ 28 * (1 + Real.log P.X) ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 28))
                (sq_nonneg _)
        _ ≤ P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14 := Env.n2
    apply sec7_le_of_sq
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 14)) hL0)
        (one_div_nonneg.mpr (mul_nonneg (pow_nonneg hx.le 2) (pow_nonneg hΩ.le 4)))
    · exact (sec7_R_pos S).le
    rw [sec7_R_sq_eval]
    calc
      (sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
          (1 / (S.x ^ 2 * S.Ω ^ 4))) ^ 2
          = (sec7_harvC ^ 2 * W ^ 28 * (1 + Real.log P.X) ^ 2) /
            (S.x ^ 4 * S.Ω ^ 8) := by
            field_simp [hx.ne', hΩ.ne']
      _ ≤ (P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14) / (S.x ^ 4 * S.Ω ^ 8) := by
            exact div_le_div_of_nonneg_right hC (by positivity)
      _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
            field_simp [hx.ne', hΩ.ne']) using 1
  field_simp [hG.ne', hΩ.ne', hx.ne']

private theorem sec7_nonzero_fit_res1 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 8 * (1 + Real.log P.X) * (S.Ω ^ 2 / P.H) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hC : sec7_harvC ^ 2 * W ^ 16 * (1 + Real.log P.X) ^ 2 ≤
      P.H ^ 3 * S.x * P.G ^ 2 * S.Ω ^ 2 := by
    calc
      sec7_harvC ^ 2 * W ^ 16 * (1 + Real.log P.X) ^ 2
          ≤ sec7_envC * W ^ 16 * (1 + Real.log P.X) ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 16))
              (sq_nonneg _)
      _ ≤ P.H ^ 3 * S.x * P.G ^ 2 * S.Ω ^ 2 := Env.res1
  apply sec7_le_of_sq
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 8)) hL0)
      (div_nonneg (pow_nonneg hΩ.le 2) hH.le)
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 8 * (1 + Real.log P.X) * (S.Ω ^ 2 / P.H)) ^ 2
        = (sec7_harvC ^ 2 * W ^ 16 * (1 + Real.log P.X) ^ 2) *
          (S.Ω ^ 4 / P.H ^ 2) := by ring
    _ ≤ (P.H ^ 3 * S.x * P.G ^ 2 * S.Ω ^ 2) * (S.Ω ^ 4 / P.H ^ 2) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          field_simp [hH.ne']

private theorem sec7_nonzero_fit_res2 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
      ((S.Ω ^ 2 / P.H) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  convert (show sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
      (1 / (P.H * P.G * S.Ω ^ 3)) ≤ S.R from by
    have hW0 : 0 ≤ W := le_trans zero_le_one hW
    have hx := OnStripAux.x_pos P S
    have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
    have hC : sec7_harvC ^ 2 * W ^ 28 * (1 + Real.log P.X) ^ 2 ≤
        P.H ^ 3 * S.x * P.G ^ 4 * S.Ω ^ 12 := by
      calc
        sec7_harvC ^ 2 * W ^ 28 * (1 + Real.log P.X) ^ 2
            ≤ sec7_envC * W ^ 28 * (1 + Real.log P.X) ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 28))
                (sq_nonneg _)
        _ ≤ P.H ^ 3 * S.x * P.G ^ 4 * S.Ω ^ 12 := Env.res2
    apply sec7_le_of_sq
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 14)) hL0)
        (one_div_nonneg.mpr (mul_nonneg (mul_nonneg hH.le hG.le) (pow_nonneg hΩ.le 3)))
    · exact (sec7_R_pos S).le
    rw [sec7_R_sq_eval]
    calc
      (sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
          (1 / (P.H * P.G * S.Ω ^ 3))) ^ 2
          = (sec7_harvC ^ 2 * W ^ 28 * (1 + Real.log P.X) ^ 2) /
            (P.H ^ 2 * P.G ^ 2 * S.Ω ^ 6) := by
            field_simp [hH.ne', hG.ne', hΩ.ne']
      _ ≤ (P.H ^ 3 * S.x * P.G ^ 4 * S.Ω ^ 12) /
            (P.H ^ 2 * P.G ^ 2 * S.Ω ^ 6) := by
            exact div_le_div_of_nonneg_right hC (by positivity)
      _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
            field_simp [hH.ne', hG.ne', hΩ.ne']) using 1
  field_simp [hH.ne', hG.ne', hΩ.ne']

private theorem sec7_nonzero_fit_n2_sden {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X)
    (hG1 : 1 ≤ P.G) :
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
      (1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hC : sec7_harvC ^ 2 * W ^ 28 * (1 + Real.log P.X) ^ 2 ≤
      P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14 := by
    calc
      sec7_harvC ^ 2 * W ^ 28 * (1 + Real.log P.X) ^ 2
          ≤ sec7_envC * W ^ 28 * (1 + Real.log P.X) ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 28))
              (sq_nonneg _)
      _ ≤ P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14 := Env.n2
  apply sec7_le_of_sq
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 14)) hL0)
      (one_div_nonneg.mpr
        (mul_nonneg (mul_nonneg (pow_nonneg hx.le 2) (pow_nonneg hG.le 2))
          (pow_nonneg hΩ.le 4)))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
        (1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4))) ^ 2
        = (sec7_harvC ^ 2 * W ^ 28 * (1 + Real.log P.X) ^ 2) /
          (S.x ^ 4 * P.G ^ 4 * S.Ω ^ 8) := by
          field_simp [hx.ne', hG.ne', hΩ.ne']
    _ ≤ (P.H * S.x ^ 5 * P.G ^ 2 * S.Ω ^ 14) /
          (S.x ^ 4 * P.G ^ 4 * S.Ω ^ 8) := by
          exact div_le_div_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * S.Ω ^ 6 / P.G ^ 2 := by
          field_simp [hx.ne', hG.ne', hΩ.ne']
    _ ≤ P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
          have hG2 : (1 : ℝ) ≤ P.G ^ 2 := by nlinarith only [hG1]
          have hdiv : 1 / P.G ^ 2 ≤ P.G ^ 2 := by
            rw [one_div]
            exact (inv_le_one_of_one_le₀ hG2).trans hG2
          have hA0 : 0 ≤ P.H * S.x * S.Ω ^ 6 := by positivity
          calc
            P.H * S.x * S.Ω ^ 6 / P.G ^ 2
                = (P.H * S.x * S.Ω ^ 6) * (1 / P.G ^ 2) := by ring
            _ ≤ (P.H * S.x * S.Ω ^ 6) * P.G ^ 2 :=
                mul_le_mul_of_nonneg_left hdiv hA0
            _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by ring

private theorem sec7_nonzero_fit_n3 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 20 * (1 + Real.log P.X) *
      ((1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := OnStripAux.x_pos P S
  convert (show sec7_harvC * W ^ 20 * (1 + Real.log P.X) *
      (1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)) ≤ S.R from by
    have hW0 : 0 ≤ W := le_trans zero_le_one hW
    have hH := P.H_pos
    have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
    have hC : sec7_harvC ^ 2 * W ^ 40 * (1 + Real.log P.X) ^ 2 ≤
        P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24 := by
      calc
        sec7_harvC ^ 2 * W ^ 40 * (1 + Real.log P.X) ^ 2
            ≤ sec7_envC * W ^ 40 * (1 + Real.log P.X) ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC (pow_nonneg hW0 40))
                (sq_nonneg _)
        _ ≤ P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24 := Env.n3
    apply sec7_le_of_sq
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 20)) hL0)
        (one_div_nonneg.mpr
          (mul_nonneg (mul_nonneg (pow_nonneg hx.le 2) (pow_nonneg hG.le 3))
            (pow_nonneg hΩ.le 9)))
    · exact (sec7_R_pos S).le
    rw [sec7_R_sq_eval]
    calc
      (sec7_harvC * W ^ 20 * (1 + Real.log P.X) *
          (1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9))) ^ 2
          = (sec7_harvC ^ 2 * W ^ 40 * (1 + Real.log P.X) ^ 2) /
            (S.x ^ 4 * P.G ^ 6 * S.Ω ^ 18) := by
            field_simp [hx.ne', hG.ne', hΩ.ne']
      _ ≤ (P.H * S.x ^ 5 * P.G ^ 8 * S.Ω ^ 24) /
            (S.x ^ 4 * P.G ^ 6 * S.Ω ^ 18) := by
            exact div_le_div_of_nonneg_right hC (by positivity)
      _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
            field_simp [hx.ne', hG.ne', hΩ.ne']) using 1
  field_simp [hG.ne', hΩ.ne', hx.ne']

private theorem sec7_nonzero_fit_tc2 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 8 * (1 + Real.log P.X) *
      (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hA : 0 ≤ P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2) := by
    exact mul_nonneg (Real.rpow_nonneg P.G_pos.le _) (Real.rpow_nonneg S.Ω_pos.le _)
  have hC : sec7_harvC * W ^ 8 * (1 + Real.log P.X) ≤
      P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (-(1:ℝ)/2) * S.Ω ^ ((1:ℝ)/2) := by
    calc
      sec7_harvC * W ^ 8 * (1 + Real.log P.X)
          ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 8)) hL0
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (-(1:ℝ)/2) * S.Ω ^ ((1:ℝ)/2) := Env.tc2
  calc
    sec7_harvC * W ^ 8 * (1 + Real.log P.X) *
        (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2))
        ≤
      (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ (-(1:ℝ)/2) *
          S.Ω ^ ((1:ℝ)/2)) *
        (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) := mul_le_mul_of_nonneg_right hC hA
    _ = S.R := sec7_nonzero_tc2_main_root_mono

private theorem sec7_nonzero_fit_tc6 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
      ((P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hA : 0 ≤ (P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) / (P.G * S.Ω ^ 5) := by
    exact div_nonneg
      (mul_nonneg (Real.rpow_nonneg P.G_pos.le _) (Real.rpow_nonneg S.Ω_pos.le _))
      (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5))
  have hC : sec7_harvC * W ^ 14 * (1 + Real.log P.X) ≤
      P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ ((1:ℝ)/2) * S.Ω ^ ((11:ℝ)/2) := by
    calc
      sec7_harvC * W ^ 14 * (1 + Real.log P.X)
          ≤ sec7_envC * W ^ 14 * (1 + Real.log P.X) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 14)) hL0
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ ((1:ℝ)/2) * S.Ω ^ ((11:ℝ)/2) := Env.tc6
  calc
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
        ((P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) / (P.G * S.Ω ^ 5))
        ≤
      (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ ((1:ℝ)/2) *
          S.Ω ^ ((11:ℝ)/2)) *
        ((P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)) / (P.G * S.Ω ^ 5)) :=
          mul_le_mul_of_nonneg_right hC hA
    _ = S.R := sec7_nonzero_tc6_main_root_fiber_mono

private theorem sec7_nonzero_fit_tc9 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 8 * (1 + Real.log P.X) * (S.x * P.G * S.Ω ^ 3) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hH := P.H_pos; have hG := P.G_pos; have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hC : sec7_harvC ^ 2 * (W ^ 16 * S.x) * (1 + Real.log P.X) ^ 2 ≤ P.H := by
    calc
      sec7_harvC ^ 2 * (W ^ 16 * S.x) * (1 + Real.log P.X) ^ 2
          ≤ sec7_envC * (W ^ 16 * S.x) * (1 + Real.log P.X) ^ 2 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC
                (mul_nonneg (pow_nonneg hW0 16) hx.le)) (sq_nonneg _)
      _ ≤ P.H := Env.tc9
  apply sec7_le_of_sq
  · exact mul_nonneg
      (mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 8)) hL0)
      (mul_nonneg (mul_nonneg hx.le hG.le) (pow_nonneg hΩ.le 3))
  · exact (sec7_R_pos S).le
  rw [sec7_R_sq_eval]
  calc
    (sec7_harvC * W ^ 8 * (1 + Real.log P.X) * (S.x * P.G * S.Ω ^ 3)) ^ 2
        = (sec7_harvC ^ 2 * (W ^ 16 * S.x) * (1 + Real.log P.X) ^ 2) *
          (S.x * P.G ^ 2 * S.Ω ^ 6) := by ring
    _ ≤ P.H * (S.x * P.G ^ 2 * S.Ω ^ 6) := by
          exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by ring

private theorem sec7_nonzero_fit_tc10 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) *
      ((S.x * P.G * S.Ω ^ 3) / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hG := P.G_pos; have hΩ := S.Ω_pos; have hx := OnStripAux.x_pos P S
  convert (show sec7_harvC * W ^ 14 * (1 + Real.log P.X) * (S.x / S.Ω ^ 2) ≤ S.R from by
    have hW0 : 0 ≤ W := le_trans zero_le_one hW
    have hH := P.H_pos
    have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
    have hC : sec7_harvC ^ 2 * (W ^ 28 * S.x) * (1 + Real.log P.X) ^ 2 ≤
        P.H * P.G ^ 2 * S.Ω ^ 10 := by
      calc
        sec7_harvC ^ 2 * (W ^ 28 * S.x) * (1 + Real.log P.X) ^ 2
            ≤ sec7_envC * (W ^ 28 * S.x) * (1 + Real.log P.X) ^ 2 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right sec7_harvC_sq_le_envC
                  (mul_nonneg (pow_nonneg hW0 28) hx.le)) (sq_nonneg _)
        _ ≤ P.H * P.G ^ 2 * S.Ω ^ 10 := Env.tc10
    apply sec7_le_of_sq
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg sec7_harvC_pos.le (pow_nonneg hW0 14)) hL0)
        (div_nonneg hx.le (pow_nonneg hΩ.le 2))
    · exact (sec7_R_pos S).le
    rw [sec7_R_sq_eval]
    calc
      (sec7_harvC * W ^ 14 * (1 + Real.log P.X) * (S.x / S.Ω ^ 2)) ^ 2
          = (sec7_harvC ^ 2 * (W ^ 28 * S.x) * (1 + Real.log P.X) ^ 2) *
            (S.x / S.Ω ^ 4) := by
            field_simp [hΩ.ne']
      _ ≤ (P.H * P.G ^ 2 * S.Ω ^ 10) * (S.x / S.Ω ^ 4) := by
            exact mul_le_mul_of_nonneg_right hC (by positivity)
      _ = P.H * S.x * P.G ^ 2 * S.Ω ^ 6 := by
            field_simp [hΩ.ne']) using 1
  field_simp [hG.ne', hΩ.ne']

private theorem sec7_nonzero_fit_tc3 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 11 * (1 + Real.log P.X) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  calc
    sec7_harvC * W ^ 11 * (1 + Real.log P.X)
        ≤ sec7_envC * W ^ 11 * (1 + Real.log P.X) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 11)) hL0
    _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := Env.tc3
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_nonzero_fit_tc7 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 17 * (1 + Real.log P.X) * (1 / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hA : 0 ≤ 1 / (P.G * S.Ω ^ 5) := by
    exact one_div_nonneg.mpr (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5))
  have hC : sec7_harvC * W ^ 17 * (1 + Real.log P.X) ≤
      P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := by
    calc
      sec7_harvC * W ^ 17 * (1 + Real.log P.X)
          ≤ sec7_envC * W ^ 17 * (1 + Real.log P.X) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 17)) hL0
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := Env.tc7
  calc
    sec7_harvC * W ^ 17 * (1 + Real.log P.X) * (1 / (P.G * S.Ω ^ 5))
        ≤ (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) *
          (1 / (P.G * S.Ω ^ 5)) := mul_le_mul_of_nonneg_right hC hA
    _ = S.R := sec7_nonzero_tc7_fiber_mono

private theorem sec7_nonzero_fit_tc4 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 8 * (1 + Real.log P.X) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  calc
    sec7_harvC * W ^ 8 * (1 + Real.log P.X)
        ≤ sec7_envC * W ^ 8 * (1 + Real.log P.X) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 8)) hL0
    _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G * S.Ω ^ 3 := Env.tc4
    _ = S.R := sec7_R_mono_nat S

private theorem sec7_nonzero_fit_tc8 {P : Globals} {S : Scale P} {W : ℝ}
    (Env : Sec7Envelope P S W) (hW : 1 ≤ W) (hlog0 : 0 ≤ Real.log P.X) :
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) * (1 / (P.G * S.Ω ^ 5)) ≤ S.R := by
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hL0 : 0 ≤ 1 + Real.log P.X := by linarith
  have hA : 0 ≤ 1 / (P.G * S.Ω ^ 5) := by
    exact one_div_nonneg.mpr (mul_nonneg P.G_pos.le (pow_nonneg S.Ω_pos.le 5))
  have hC : sec7_harvC * W ^ 14 * (1 + Real.log P.X) ≤
      P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := by
    calc
      sec7_harvC * W ^ 14 * (1 + Real.log P.X)
          ≤ sec7_envC * W ^ 14 * (1 + Real.log P.X) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right sec7_harvC_le_envC (pow_nonneg hW0 14)) hL0
      _ ≤ P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8 := Env.tc8
  calc
    sec7_harvC * W ^ 14 * (1 + Real.log P.X) * (1 / (P.G * S.Ω ^ 5))
        ≤ (P.H ^ ((1:ℝ)/2) * S.x ^ ((1:ℝ)/2) * P.G ^ 2 * S.Ω ^ 8) *
          (1 / (P.G * S.Ω ^ 5)) := mul_le_mul_of_nonneg_right hC hA
    _ = S.R := sec7_nonzero_tc7_fiber_mono

private theorem sec7_add18_le
    {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 : ℝ}
    {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 : ℝ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) (h4 : a4 ≤ b4)
    (h5 : a5 ≤ b5) (h6 : a6 ≤ b6) (h7 : a7 ≤ b7) (h8 : a8 ≤ b8)
    (h9 : a9 ≤ b9) (h10 : a10 ≤ b10) (h11 : a11 ≤ b11)
    (h12 : a12 ≤ b12) (h13 : a13 ≤ b13) (h14 : a14 ≤ b14)
    (h15 : a15 ≤ b15) (h16 : a16 ≤ b16) (h17 : a17 ≤ b17)
    (h18 : a18 ≤ b18) :
    a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 +
      a13 + a14 + a15 + a16 + a17 + a18 ≤
    b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 +
      b13 + b14 + b15 + b16 + b17 + b18 := by
  linarith

private theorem sec7_add16_le
    {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : ℝ}
    {b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : ℝ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) (h4 : a4 ≤ b4)
    (h5 : a5 ≤ b5) (h6 : a6 ≤ b6) (h7 : a7 ≤ b7) (h8 : a8 ≤ b8)
    (h9 : a9 ≤ b9) (h10 : a10 ≤ b10) (h11 : a11 ≤ b11)
    (h12 : a12 ≤ b12) (h13 : a13 ≤ b13) (h14 : a14 ≤ b14)
    (h15 : a15 ≤ b15) (h16 : a16 ≤ b16) :
    a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 + a11 + a12 +
      a13 + a14 + a15 + a16 ≤
    b1 + b2 + b3 + b4 + b5 + b6 + b7 + b8 + b9 + b10 + b11 + b12 +
      b13 + b14 + b15 + b16 := by
  linarith

/- md 1740–81 (per-triple zero-branch inputs, fixed triple in the box):
   "Lemma 4.2 gives  R√(δ₀/T_{ρ,u}) ≪ H^{1/4}x^{1/4}G^{5/2}Ω^{13/2}P^{-1/2},
    R√((S/(Rx²G²Ω⁴))/T_{ρ,u}) ≪ H^{1/4}x^{1/4}GΩ⁴(S/P)^{1/2},  and
    T_{ρ,u} ≪ hΣ/(x²G²Ω⁴) + P/(x²G³Ω⁹).  Together with
    Rδ₁(h) ≪ GΩ/x² + Ω²/H + S/(x²G²Ω⁴)  (7.6),  the fiber count (7.2)
    [u-fibres O(1+S/(GΩ⁵)), carries ρ = O(1)], and the offset contribution
    (1+S/(GΩ⁵))·hΣT₁/R, we sum over the whole rectangular shift box."
   md 1782–1803: the eleven elementary sums (= N14).  md 1797–1825: "Comparing the
   resulting total upper bound with the averaged cube lower bound ≫ R/W gives the old
   nine constraints and the two extra offset constraints (7.7) [envelope n1–n9, off1–off2].
   The extra Ω²/H term in (7.6) is kept without absorption … it gives the four
   no-absorption residual constraints [envelope res1–res4]." -/
/-- **N15** (md 1770–1825): zero-top-carry harvest. Any per-triple count `cnt` satisfying
the evaluated N13-branch bound sums over the box to at most `(R/W)/sec7_harvM` under the
envelope. This is the zero-branch count bound the N23 contradiction consumes.
PHASE-1f SEAM: the two root terms are in N13's literal `Real.sqrt` forms
(`…/√P` and `…·√(S/P)`, `sec7_zero_triple_count`), not `rpow`. -/
theorem sec7_harvest_zero :
    ∀ (P : Globals) (S : Scale P) (W : ℝ), Sec7Envelope P S W → 1 ≤ W →
    ∀ c₀ Cu : ℝ, OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
    0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
    ∀ cnt : ℕ × ℕ × ℕ → ℝ,
      (∀ p ∈ box W,
        cnt p ≤ sec7_cTriple * (1 + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (P.G * S.Ω ^ 5)) *
          (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
            + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
            + P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)
                / Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ)
            + P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4
                * Real.sqrt ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ))
            + (HSbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
            + (Pbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)
            + 1
            + (HSbox p.1 p.2.1 p.2.2 : ℝ) * S.T₁ / S.R)) →
      (∑ p ∈ box W, cnt p) ≤ S.R / (W * sec7_harvM) := by
  intro P S W Env hW c₀ Cu hsd hbud hg0 hu0 hX24 cnt hcnt
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hlog0 : 0 ≤ Real.log P.X := Real.log_nonneg hsd.hX
  have hG1 : 1 ≤ P.G := sec7_G_ge_one hsd.hX hg0
  rcases sec7_box_sums_zero W hW with
    ⟨h1, hS, hS2, hP, hSP, _hPm, _hSPm, _hSqrt, _hSSqrt, hHS, hSHS⟩
  rcases sec7_box_sums_zero_sqrt W hW with
    ⟨hInvSqrt, hSInvSqrt, hSqrtSP, hSSqrtSP⟩
  let A₁ : ℝ := P.G * S.Ω / S.x ^ 2
  let A₂ : ℝ := S.Ω ^ 2 / P.H
  let A₃ : ℝ := 1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
  let A₄ : ℝ :=
    P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
      P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)
  let A₅ : ℝ := P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4
  let A₇ : ℝ := 1 / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)
  let A₉ : ℝ := S.T₁ / S.R
  let F₁ : ℝ := A₁ / (P.G * S.Ω ^ 5)
  let F₂ : ℝ := A₂ / (P.G * S.Ω ^ 5)
  let F₃ : ℝ := A₃ / (P.G * S.Ω ^ 5)
  let F₄ : ℝ := A₄ / (P.G * S.Ω ^ 5)
  let F₅ : ℝ := A₅ / (P.G * S.Ω ^ 5)
  let F₇ : ℝ := A₇ / (P.G * S.Ω ^ 5)
  let F₀ : ℝ := 1 / (P.G * S.Ω ^ 5)
  let F₉ : ℝ := A₉ / (P.G * S.Ω ^ 5)
  let E : ℕ × ℕ × ℕ → ℝ := fun p =>
    (1 : ℝ) * A₁
      + (1 : ℝ) * A₂
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * A₃
      + (1 / Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ)) * A₄
      + Real.sqrt ((Sbox p.1 p.2.1 p.2.2 : ℝ) /
          (Pbox p.1 p.2.1 p.2.2 : ℝ)) * A₅
      + (HSbox p.1 p.2.1 p.2.2 : ℝ) * A₃
      + (Pbox p.1 p.2.1 p.2.2 : ℝ) * A₇
      + (1 : ℝ) * 1
      + (HSbox p.1 p.2.1 p.2.2 : ℝ) * A₉
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * F₁
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * F₂
      + ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ 2) * F₃
      + ((Sbox p.1 p.2.1 p.2.2 : ℝ) /
          Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ)) * F₄
      + ((Sbox p.1 p.2.1 p.2.2 : ℝ) *
          Real.sqrt ((Sbox p.1 p.2.1 p.2.2 : ℝ) /
            (Pbox p.1 p.2.1 p.2.2 : ℝ))) * F₅
      + ((Sbox p.1 p.2.1 p.2.2 : ℝ) *
          (HSbox p.1 p.2.1 p.2.2 : ℝ)) * F₃
      + ((Sbox p.1 p.2.1 p.2.2 : ℝ) *
          (Pbox p.1 p.2.1 p.2.2 : ℝ)) * F₇
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * F₀
      + ((Sbox p.1 p.2.1 p.2.2 : ℝ) *
          (HSbox p.1 p.2.1 p.2.2 : ℝ)) * F₉
  let Z : ℝ :=
    W ^ 7 * A₁
      + W ^ 7 * A₂
      + W ^ 13 * A₃
      + W ^ ((7:ℝ)/2) * A₄
      + W ^ ((13:ℝ)/2) * A₅
      + W ^ 11 * A₃
      + W ^ 14 * A₇
      + W ^ 7 * 1
      + W ^ 11 * A₉
      + W ^ 13 * F₁
      + W ^ 13 * F₂
      + W ^ 19 * F₃
      + W ^ ((19:ℝ)/2) * F₄
      + W ^ ((25:ℝ)/2) * F₅
      + W ^ 17 * F₃
      + W ^ 20 * F₇
      + W ^ 13 * F₀
      + W ^ 17 * F₉
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  have hA₃ : 0 ≤ A₃ := by dsimp [A₃]; positivity
  have hA₄ : 0 ≤ A₄ := by
    dsimp [A₄]
    positivity
  have hA₅ : 0 ≤ A₅ := by
    dsimp [A₅]
    positivity
  have hA₇ : 0 ≤ A₇ := by dsimp [A₇]; positivity
  have hA₉ : 0 ≤ A₉ := by
    dsimp [A₉]
    exact div_nonneg (sec7_T₁_pos_local S).le (sec7_R_pos S).le
  have hF₁ : 0 ≤ F₁ := by dsimp [F₁]; positivity
  have hF₂ : 0 ≤ F₂ := by dsimp [F₂]; positivity
  have hF₃ : 0 ≤ F₃ := by dsimp [F₃]; positivity
  have hF₄ : 0 ≤ F₄ := by dsimp [F₄]; positivity
  have hF₅ : 0 ≤ F₅ := by dsimp [F₅]; positivity
  have hF₇ : 0 ≤ F₇ := by dsimp [F₇]; positivity
  have hF₀ : 0 ≤ F₀ := by dsimp [F₀]; positivity
  have hF₉ : 0 ≤ F₉ := by dsimp [F₉]; positivity
  have hpoint : ∀ p ∈ box W, cnt p ≤ sec7_cTriple * E p := by
    intro p hp
    calc
      cnt p ≤ sec7_cTriple * (1 + (Sbox p.1 p.2.1 p.2.2 : ℝ) /
          (P.G * S.Ω ^ 5)) *
        (P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
          + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
          + P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G ^ ((5:ℝ)/2) *
              S.Ω ^ ((13:ℝ)/2) / Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ)
          + P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4 *
              Real.sqrt ((Sbox p.1 p.2.1 p.2.2 : ℝ) /
                (Pbox p.1 p.2.1 p.2.2 : ℝ))
          + (HSbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
          + (Pbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 3 * S.Ω ^ 9)
          + 1 + (HSbox p.1 p.2.1 p.2.2 : ℝ) * S.T₁ / S.R) := hcnt p hp
      _ = sec7_cTriple * E p := by
        dsimp [E, A₁, A₂, A₃, A₄, A₅, A₇, A₉, F₁, F₂, F₃, F₄, F₅, F₇, F₀, F₉]
        ring
  have hsum0 :
      (∑ p ∈ box W, cnt p) ≤ (∑ p ∈ box W, sec7_cTriple * E p) :=
    Finset.sum_le_sum hpoint
  have hE₁ := sec7_sum_weight_le (box W) (fun _p : ℕ × ℕ × ℕ => (1 : ℝ))
    (A := A₁) (B := W ^ 7) hA₁ h1
  have hE₂ := sec7_sum_weight_le (box W) (fun _p : ℕ × ℕ × ℕ => (1 : ℝ))
    (A := A₂) (B := W ^ 7) hA₂ h1
  have hE₃ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := A₃) (B := W ^ 13) hA₃ hS
  have hE₄ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => 1 / Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ))
    (A := A₄) (B := W ^ ((7:ℝ)/2)) hA₄ hInvSqrt
  have hE₅ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => Real.sqrt
      ((Sbox p.1 p.2.1 p.2.2 : ℝ) / (Pbox p.1 p.2.1 p.2.2 : ℝ)))
    (A := A₅) (B := W ^ ((13:ℝ)/2)) hA₅ hSqrtSP
  have hE₆ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (HSbox p.1 p.2.1 p.2.2 : ℝ))
    (A := A₃) (B := W ^ 11) hA₃ hHS
  have hE₇ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Pbox p.1 p.2.1 p.2.2 : ℝ))
    (A := A₇) (B := W ^ 14) hA₇ hP
  have hE₈ := sec7_sum_weight_le (box W) (fun _p : ℕ × ℕ × ℕ => (1 : ℝ))
    (A := (1 : ℝ)) (B := W ^ 7) (by norm_num) h1
  have hE₉ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (HSbox p.1 p.2.1 p.2.2 : ℝ))
    (A := A₉) (B := W ^ 11) hA₉ hHS
  have hE₁₀ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := F₁) (B := W ^ 13) hF₁ hS
  have hE₁₁ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := F₂) (B := W ^ 13) hF₂ hS
  have hE₁₂ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ 2)
    (A := F₃) (B := W ^ 19) hF₃ hS2
  have hE₁₃ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ) /
      Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ))
    (A := F₄) (B := W ^ ((19:ℝ)/2)) hF₄ hSInvSqrt
  have hE₁₄ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ) *
      Real.sqrt ((Sbox p.1 p.2.1 p.2.2 : ℝ) /
        (Pbox p.1 p.2.1 p.2.2 : ℝ)))
    (A := F₅) (B := W ^ ((25:ℝ)/2)) hF₅ hSSqrtSP
  have hE₁₅ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ) *
      (HSbox p.1 p.2.1 p.2.2 : ℝ))
    (A := F₃) (B := W ^ 17) hF₃ hSHS
  have hE₁₆ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ) *
      (Pbox p.1 p.2.1 p.2.2 : ℝ))
    (A := F₇) (B := W ^ 20) hF₇ hSP
  have hE₁₇ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := F₀) (B := W ^ 13) hF₀ hS
  have hE₁₈ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ) *
      (HSbox p.1 p.2.1 p.2.2 : ℝ))
    (A := F₉) (B := W ^ 17) hF₉ hSHS
  have hsum_bound :
      (∑ p ∈ box W, cnt p) ≤ sec7_cTriple * sec7_cBox * Z := by
    calc
      (∑ p ∈ box W, cnt p) ≤ (∑ p ∈ box W, sec7_cTriple * E p) := hsum0
      _ =
          (∑ p ∈ box W, sec7_cTriple * ((1 : ℝ) * A₁))
        + (∑ p ∈ box W, sec7_cTriple * ((1 : ℝ) * A₂))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * A₃))
        + (∑ p ∈ box W, sec7_cTriple *
            ((1 / Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ)) * A₄))
        + (∑ p ∈ box W, sec7_cTriple *
            (Real.sqrt ((Sbox p.1 p.2.1 p.2.2 : ℝ) /
              (Pbox p.1 p.2.1 p.2.2 : ℝ)) * A₅))
        + (∑ p ∈ box W, sec7_cTriple * ((HSbox p.1 p.2.1 p.2.2 : ℝ) * A₃))
        + (∑ p ∈ box W, sec7_cTriple * ((Pbox p.1 p.2.1 p.2.2 : ℝ) * A₇))
        + (∑ p ∈ box W, sec7_cTriple * ((1 : ℝ) * 1))
        + (∑ p ∈ box W, sec7_cTriple * ((HSbox p.1 p.2.1 p.2.2 : ℝ) * A₉))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * F₁))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * F₂))
        + (∑ p ∈ box W, sec7_cTriple * (((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ 2) * F₃))
        + (∑ p ∈ box W, sec7_cTriple *
            (((Sbox p.1 p.2.1 p.2.2 : ℝ) /
              Real.sqrt (Pbox p.1 p.2.1 p.2.2 : ℝ)) * F₄))
        + (∑ p ∈ box W, sec7_cTriple *
            (((Sbox p.1 p.2.1 p.2.2 : ℝ) *
              Real.sqrt ((Sbox p.1 p.2.1 p.2.2 : ℝ) /
                (Pbox p.1 p.2.1 p.2.2 : ℝ))) * F₅))
        + (∑ p ∈ box W, sec7_cTriple *
            (((Sbox p.1 p.2.1 p.2.2 : ℝ) *
              (HSbox p.1 p.2.1 p.2.2 : ℝ)) * F₃))
        + (∑ p ∈ box W, sec7_cTriple *
            (((Sbox p.1 p.2.1 p.2.2 : ℝ) *
              (Pbox p.1 p.2.1 p.2.2 : ℝ)) * F₇))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * F₀))
        + (∑ p ∈ box W, sec7_cTriple *
            (((Sbox p.1 p.2.1 p.2.2 : ℝ) *
              (HSbox p.1 p.2.1 p.2.2 : ℝ)) * F₉)) := by
          repeat rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          dsimp [E]
          ring_nf
      _ ≤
          sec7_cTriple * sec7_cBox * (W ^ 7 * A₁)
        + sec7_cTriple * sec7_cBox * (W ^ 7 * A₂)
        + sec7_cTriple * sec7_cBox * (W ^ 13 * A₃)
        + sec7_cTriple * sec7_cBox * (W ^ ((7:ℝ)/2) * A₄)
        + sec7_cTriple * sec7_cBox * (W ^ ((13:ℝ)/2) * A₅)
        + sec7_cTriple * sec7_cBox * (W ^ 11 * A₃)
        + sec7_cTriple * sec7_cBox * (W ^ 14 * A₇)
        + sec7_cTriple * sec7_cBox * (W ^ 7 * 1)
        + sec7_cTriple * sec7_cBox * (W ^ 11 * A₉)
        + sec7_cTriple * sec7_cBox * (W ^ 13 * F₁)
        + sec7_cTriple * sec7_cBox * (W ^ 13 * F₂)
        + sec7_cTriple * sec7_cBox * (W ^ 19 * F₃)
        + sec7_cTriple * sec7_cBox * (W ^ ((19:ℝ)/2) * F₄)
        + sec7_cTriple * sec7_cBox * (W ^ ((25:ℝ)/2) * F₅)
        + sec7_cTriple * sec7_cBox * (W ^ 17 * F₃)
        + sec7_cTriple * sec7_cBox * (W ^ 20 * F₇)
        + sec7_cTriple * sec7_cBox * (W ^ 13 * F₀)
        + sec7_cTriple * sec7_cBox * (W ^ 17 * F₉) := by
          exact sec7_add18_le hE₁ hE₂ hE₃ hE₄ hE₅ hE₆ hE₇ hE₈ hE₉
            hE₁₀ hE₁₁ hE₁₂ hE₁₃ hE₁₄ hE₁₅ hE₁₆ hE₁₇ hE₁₈
      _ = sec7_cTriple * sec7_cBox * Z := by
          dsimp [Z]
          ring
  have hslice₁ : sec7_cTriple * sec7_cBox * (W ^ 7 * A₁) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_z1 Env hW hlog0 using 1
    dsimp [A₁]
    ring
  have hslice₂ : sec7_cTriple * sec7_cBox * (W ^ 7 * A₂) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_res1 Env hW hlog0 using 1
    dsimp [A₂]
    ring
  have hslice₃ : sec7_cTriple * sec7_cBox * (W ^ 13 * A₃) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_n2_base Env hW hlog0 hG1 using 1
    dsimp [A₃]
    ring
  have hslice₄ : sec7_cTriple * sec7_cBox * (W ^ ((7:ℝ)/2) * A₄) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    dsimp [A₄]
    calc
      sec7_harvC * W *
          (W ^ ((7:ℝ)/2) *
            (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
              P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)))
          =
        sec7_harvC * (W * W ^ ((7:ℝ)/2)) *
            (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
              P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)) := by
            ring
      _ =
        sec7_harvC * W ^ ((9:ℝ)/2) *
            (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
              P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)) := by
            rw [sec7_mul_rpow hWpos ((7:ℝ)/2) ((9:ℝ)/2) (by norm_num)]
      _ ≤ S.R := sec7_zero_fit_n4 Env hW
  have hslice₅ : sec7_cTriple * sec7_cBox * (W ^ ((13:ℝ)/2) * A₅) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    dsimp [A₅]
    calc
      sec7_harvC * W *
          (W ^ ((13:ℝ)/2) *
            (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4))
          =
        sec7_harvC * (W * W ^ ((13:ℝ)/2)) *
            (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4) := by
            ring
      _ =
        sec7_harvC * W ^ ((15:ℝ)/2) *
            (P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4) := by
            rw [sec7_mul_rpow hWpos ((13:ℝ)/2) ((15:ℝ)/2) (by norm_num)]
      _ ≤ S.R := sec7_zero_fit_n6 Env hW
  have hslice₆ : sec7_cTriple * sec7_cBox * (W ^ 11 * A₃) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_off1_den Env hW using 1
    dsimp [A₃]
    ring
  have hslice₇ : sec7_cTriple * sec7_cBox * (W ^ 14 * A₇) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_n8 Env hW using 1
    dsimp [A₇]
    ring
  have hslice₈ : sec7_cTriple * sec7_cBox * (W ^ 7 * 1) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_tc4 Env hW hlog0 using 1
    ring
  have hslice₉ : sec7_cTriple * sec7_cBox * (W ^ 11 * A₉) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_off1 Env hW using 1
    dsimp [A₉]
    ring
  have hslice₁₀ : sec7_cTriple * sec7_cBox * (W ^ 13 * F₁) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_z1_fiber_raw Env hW hlog0 using 1
    dsimp [F₁, A₁]
    ring
  have hslice₁₁ : sec7_cTriple * sec7_cBox * (W ^ 13 * F₂) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_res2_raw Env hW hlog0 using 1
    dsimp [F₂, A₂]
    ring
  have hslice₁₂ : sec7_cTriple * sec7_cBox * (W ^ 19 * F₃) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_n3_raw Env hW hlog0 using 1
    dsimp [F₃, A₃]
    ring
  have hslice₁₃ : sec7_cTriple * sec7_cBox * (W ^ ((19:ℝ)/2) * F₄) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    dsimp [F₄, A₄]
    calc
      sec7_harvC * W *
          (W ^ ((19:ℝ)/2) *
            ((P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
              P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)) / (P.G * S.Ω ^ 5)))
          =
        sec7_harvC * (W * W ^ ((19:ℝ)/2)) *
            ((P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
              P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)) / (P.G * S.Ω ^ 5)) := by
            ring
      _ =
        sec7_harvC * W ^ ((21:ℝ)/2) *
            ((P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) *
              P.G ^ ((5:ℝ)/2) * S.Ω ^ ((13:ℝ)/2)) / (P.G * S.Ω ^ 5)) := by
            rw [sec7_mul_rpow hWpos ((19:ℝ)/2) ((21:ℝ)/2) (by norm_num)]
      _ ≤ S.R := sec7_zero_fit_n5_raw Env hW
  have hslice₁₄ : sec7_cTriple * sec7_cBox * (W ^ ((25:ℝ)/2) * F₅) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    dsimp [F₅, A₅]
    calc
      sec7_harvC * W *
          (W ^ ((25:ℝ)/2) *
            ((P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4) /
              (P.G * S.Ω ^ 5)))
          =
        sec7_harvC * (W * W ^ ((25:ℝ)/2)) *
            ((P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4) /
              (P.G * S.Ω ^ 5)) := by
            ring
      _ =
        sec7_harvC * W ^ ((27:ℝ)/2) *
            ((P.H ^ ((1:ℝ)/4) * S.x ^ ((1:ℝ)/4) * P.G * S.Ω ^ 4) /
              (P.G * S.Ω ^ 5)) := by
            rw [sec7_mul_rpow hWpos ((25:ℝ)/2) ((27:ℝ)/2) (by norm_num)]
      _ ≤ S.R := sec7_zero_fit_n7_raw Env hW
  have hslice₁₅ : sec7_cTriple * sec7_cBox * (W ^ 17 * F₃) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_off2_den_raw Env hW using 1
    dsimp [F₃, A₃]
    ring
  have hslice₁₆ : sec7_cTriple * sec7_cBox * (W ^ 20 * F₇) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_n9_raw Env hW using 1
    dsimp [F₇, A₇]
    ring
  have hslice₁₇ : sec7_cTriple * sec7_cBox * (W ^ 13 * F₀) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_tc8 Env hW hlog0 using 1
    dsimp [F₀]
    ring
  have hslice₁₈ : sec7_cTriple * sec7_cBox * (W ^ 17 * F₉) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_zero_fit_off2 Env hW using 1
    dsimp [F₉, A₉]
    ring
  have hZ :
      sec7_cTriple * sec7_cBox * Z ≤ S.R / (W * sec7_harvM) := by
    let D : ℝ := S.R / (18 * (W * sec7_harvM))
    have hsumSlices : sec7_cTriple * sec7_cBox * Z ≤ 18 * D := by
      calc
        sec7_cTriple * sec7_cBox * Z =
            sec7_cTriple * sec7_cBox * (W ^ 7 * A₁)
          + sec7_cTriple * sec7_cBox * (W ^ 7 * A₂)
          + sec7_cTriple * sec7_cBox * (W ^ 13 * A₃)
          + sec7_cTriple * sec7_cBox * (W ^ ((7:ℝ)/2) * A₄)
          + sec7_cTriple * sec7_cBox * (W ^ ((13:ℝ)/2) * A₅)
          + sec7_cTriple * sec7_cBox * (W ^ 11 * A₃)
          + sec7_cTriple * sec7_cBox * (W ^ 14 * A₇)
          + sec7_cTriple * sec7_cBox * (W ^ 7 * 1)
          + sec7_cTriple * sec7_cBox * (W ^ 11 * A₉)
          + sec7_cTriple * sec7_cBox * (W ^ 13 * F₁)
          + sec7_cTriple * sec7_cBox * (W ^ 13 * F₂)
          + sec7_cTriple * sec7_cBox * (W ^ 19 * F₃)
          + sec7_cTriple * sec7_cBox * (W ^ ((19:ℝ)/2) * F₄)
          + sec7_cTriple * sec7_cBox * (W ^ ((25:ℝ)/2) * F₅)
          + sec7_cTriple * sec7_cBox * (W ^ 17 * F₃)
          + sec7_cTriple * sec7_cBox * (W ^ 20 * F₇)
          + sec7_cTriple * sec7_cBox * (W ^ 13 * F₀)
          + sec7_cTriple * sec7_cBox * (W ^ 17 * F₉) := by
            dsimp [Z]
            ring
        _ ≤ D + D + D + D + D + D + D + D + D + D + D + D + D + D + D + D + D + D := by
            exact sec7_add18_le hslice₁ hslice₂ hslice₃ hslice₄ hslice₅ hslice₆
              hslice₇ hslice₈ hslice₉ hslice₁₀ hslice₁₁ hslice₁₂ hslice₁₃
              hslice₁₄ hslice₁₅ hslice₁₆ hslice₁₇ hslice₁₈
        _ = 18 * D := by ring
    calc
      sec7_cTriple * sec7_cBox * Z ≤ 18 * D := hsumSlices
      _ = S.R / (W * sec7_harvM) := by
        dsimp [D]
        field_simp [hWpos.ne', sec7_harvM_pos.ne']
  exact hsum_bound.trans hZ

/- md 1936–74 (per-triple nonzero-branch inputs): "Summing (7.8) over the whole rectangular
   shift box, multiplying by the fiber count (7.2), using (7.6), and comparing with the
   averaged cube lower bound ≫ R/W, we use ∑1 ≪ W⁷, ∑S ≪ W¹³, ∑S^{1/2} ≪ W¹⁰,
   ∑S^{3/2} ≪ W¹⁶ [= N21]. This gives the additional constraints
   [the eight md 1944–66 displays = envelope tc1–tc8]. The displayed residual square-root
   term gives in addition  W⁸ ≪ H^{1/2}x^{-1/2},  W¹⁴ ≪ H^{1/2}x^{-1/2}GΩ⁵
   [roots of tc9–tc10]. Taking roots gives exactly the new constraints listed in the
   statement, apart from those already present in the ρ₀ = 0 branch."
   The (7.8) terms enter in their N20-evaluated `R ≍ R₀` form; the N19 `(1 + log X)`
   factor is absorbed here against the strip's X-slack (TRAP-2 shrink-c). -/
/-- **N22** (md 1942–74): nonzero-top-carry harvest. Any per-triple count `cnt` satisfying
the evaluated N19/N20-branch bound (with the Prop 4.3 log factor) sums over the box to at
most `(R/W)/sec7_harvM` under the envelope. This is the nonzero-branch count bound the
N23 contradiction consumes.
PHASE-1f SEAM: the residual root term is in N20's literal form `Real.sqrt S`
(`sec7_nonzero_sqrt_evals`, fourth evaluation at `Sv := Sbox`), not `rpow`. -/
theorem sec7_harvest_nonzero :
    ∀ (P : Globals) (S : Scale P) (W : ℝ), Sec7Envelope P S W → 1 ≤ W →
    ∀ c₀ Cu : ℝ, OnStripAux.StripData P S c₀ Cu → OnStripAux.Budget P.g P.u Cu →
    0 ≤ P.g → 0 < P.u → (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
    ∀ cnt : ℕ × ℕ × ℕ → ℝ,
      (∀ p ∈ box W,
        cnt p ≤ sec7_cTriple * (1 + Real.log P.X)
          * (1 + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (P.G * S.Ω ^ 5)) *
          (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)
            + P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
            + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
            + P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)
            + S.x * P.G * S.Ω ^ 3
            + Real.sqrt (Sbox p.1 p.2.1 p.2.2 : ℝ)
            + 1)) →
      (∑ p ∈ box W, cnt p) ≤ S.R / (W * sec7_harvM) := by
  intro P S W Env hW c₀ Cu hsd hbud hg0 hu0 hX24 cnt hcnt
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hH := P.H_pos
  have hG := P.G_pos
  have hΩ := S.Ω_pos
  have hx := OnStripAux.x_pos P S
  have hlog0 : 0 ≤ Real.log P.X := Real.log_nonneg hsd.hX
  have hG1 : 1 ≤ P.G := sec7_G_ge_one hsd.hX hg0
  rcases sec7_box_sums_nonzero W hW with ⟨h1, hS, hSsqrt, hSthalf⟩
  rcases sec7_box_sums_zero W hW with
    ⟨_, _, hS2, _, _, _, _, _, _, _, _⟩
  have hSsqrtNat :
      (∑ p ∈ box W, (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((1:ℝ)/2))
        ≤ sec7_cBox * W ^ 10 := by
    convert hSsqrt using 1
    rw [show (10:ℝ) = ((10:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hSthalfNat :
      (∑ p ∈ box W, (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((3:ℝ)/2))
        ≤ sec7_cBox * W ^ 16 := by
    convert hSthalf using 1
    rw [show (16:ℝ) = ((16:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  let L : ℝ := 1 + Real.log P.X
  let A₁ : ℝ := P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)
  let A₂ : ℝ := P.G * S.Ω / S.x ^ 2
  let A₃ : ℝ := S.Ω ^ 2 / P.H
  let A₄ : ℝ := 1 / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
  let A₅ : ℝ := P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)
  let A₆ : ℝ := S.x * P.G * S.Ω ^ 3
  let F₁ : ℝ := A₁ / (P.G * S.Ω ^ 5)
  let F₂ : ℝ := A₂ / (P.G * S.Ω ^ 5)
  let F₃ : ℝ := A₃ / (P.G * S.Ω ^ 5)
  let F₄ : ℝ := A₄ / (P.G * S.Ω ^ 5)
  let F₅ : ℝ := A₅ / (P.G * S.Ω ^ 5)
  let F₆ : ℝ := A₆ / (P.G * S.Ω ^ 5)
  let F₇ : ℝ := 1 / (P.G * S.Ω ^ 5)
  let F₈ : ℝ := 1 / (P.G * S.Ω ^ 5)
  let E : ℕ × ℕ × ℕ → ℝ := fun p =>
    (1 : ℝ) * (L * A₁)
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₁)
      + (1 : ℝ) * (L * A₂)
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₂)
      + (1 : ℝ) * (L * A₃)
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₃)
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * A₄)
      + ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ 2) * (L * F₄)
      + (1 : ℝ) * (L * A₅)
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₅)
      + (1 : ℝ) * (L * A₆)
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₆)
      + ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((1:ℝ)/2)) * (L * 1)
      + ((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((3:ℝ)/2)) * (L * F₇)
      + (1 : ℝ) * (L * 1)
      + (Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₈)
  let Z : ℝ :=
    W ^ 7 * (L * A₁)
      + W ^ 13 * (L * F₁)
      + W ^ 7 * (L * A₂)
      + W ^ 13 * (L * F₂)
      + W ^ 7 * (L * A₃)
      + W ^ 13 * (L * F₃)
      + W ^ 13 * (L * A₄)
      + W ^ 19 * (L * F₄)
      + W ^ 7 * (L * A₅)
      + W ^ 13 * (L * F₅)
      + W ^ 7 * (L * A₆)
      + W ^ 13 * (L * F₆)
      + W ^ 10 * (L * 1)
      + W ^ 16 * (L * F₇)
      + W ^ 7 * (L * 1)
      + W ^ 13 * (L * F₈)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hA₁ : 0 ≤ A₁ := by
    dsimp [A₁]
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hH.le _) (Real.rpow_nonneg hx.le _))
      (Real.rpow_nonneg hΩ.le _)
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  have hA₃ : 0 ≤ A₃ := by dsimp [A₃]; positivity
  have hA₄ : 0 ≤ A₄ := by dsimp [A₄]; positivity
  have hA₅ : 0 ≤ A₅ := by
    dsimp [A₅]
    exact mul_nonneg (Real.rpow_nonneg hG.le _) (Real.rpow_nonneg hΩ.le _)
  have hA₆ : 0 ≤ A₆ := by dsimp [A₆]; positivity
  have hF₁ : 0 ≤ F₁ := by
    dsimp [F₁]
    exact div_nonneg hA₁ (mul_nonneg hG.le (pow_nonneg hΩ.le 5))
  have hF₂ : 0 ≤ F₂ := by dsimp [F₂]; positivity
  have hF₃ : 0 ≤ F₃ := by dsimp [F₃]; positivity
  have hF₄ : 0 ≤ F₄ := by dsimp [F₄]; positivity
  have hF₅ : 0 ≤ F₅ := by dsimp [F₅]; exact div_nonneg hA₅ (mul_nonneg hG.le (pow_nonneg hΩ.le 5))
  have hF₆ : 0 ≤ F₆ := by dsimp [F₆]; positivity
  have hF₇ : 0 ≤ F₇ := by dsimp [F₇]; positivity
  have hF₈ : 0 ≤ F₈ := by dsimp [F₈]; positivity
  have hLA₁ : 0 ≤ L * A₁ := mul_nonneg hL0 hA₁
  have hLF₁ : 0 ≤ L * F₁ := mul_nonneg hL0 hF₁
  have hLA₂ : 0 ≤ L * A₂ := mul_nonneg hL0 hA₂
  have hLF₂ : 0 ≤ L * F₂ := mul_nonneg hL0 hF₂
  have hLA₃ : 0 ≤ L * A₃ := mul_nonneg hL0 hA₃
  have hLF₃ : 0 ≤ L * F₃ := mul_nonneg hL0 hF₃
  have hLA₄ : 0 ≤ L * A₄ := mul_nonneg hL0 hA₄
  have hLF₄ : 0 ≤ L * F₄ := mul_nonneg hL0 hF₄
  have hLA₅ : 0 ≤ L * A₅ := mul_nonneg hL0 hA₅
  have hLF₅ : 0 ≤ L * F₅ := mul_nonneg hL0 hF₅
  have hLA₆ : 0 ≤ L * A₆ := mul_nonneg hL0 hA₆
  have hLF₆ : 0 ≤ L * F₆ := mul_nonneg hL0 hF₆
  have hL1 : 0 ≤ L * 1 := by simpa using hL0
  have hLF₇ : 0 ≤ L * F₇ := mul_nonneg hL0 hF₇
  have hLF₈ : 0 ≤ L * F₈ := mul_nonneg hL0 hF₈
  have hpoint : ∀ p ∈ box W, cnt p ≤ sec7_cTriple * E p := by
    intro p hp
    calc
      cnt p ≤ sec7_cTriple * (1 + Real.log P.X)
          * (1 + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (P.G * S.Ω ^ 5)) *
          (P.H ^ ((1:ℝ)/3) * S.x ^ (-(1:ℝ)/3) * S.Ω ^ ((2:ℝ)/3)
            + P.G * S.Ω / S.x ^ 2 + S.Ω ^ 2 / P.H
            + (Sbox p.1 p.2.1 p.2.2 : ℝ) / (S.x ^ 2 * P.G ^ 2 * S.Ω ^ 4)
            + P.G ^ ((3:ℝ)/2) * S.Ω ^ ((5:ℝ)/2)
            + S.x * P.G * S.Ω ^ 3
            + Real.sqrt (Sbox p.1 p.2.1 p.2.2 : ℝ)
            + 1) := hcnt p hp
      _ = sec7_cTriple * E p := by
        dsimp [E, L, A₁, A₂, A₃, A₄, A₅, A₆, F₁, F₂, F₃, F₄, F₅, F₆, F₇, F₈]
        rw [Real.sqrt_eq_rpow, ← sec7_Sbox_mul_sqrt_eq hp]
        ring
  have hsum0 :
      (∑ p ∈ box W, cnt p) ≤ (∑ p ∈ box W, sec7_cTriple * E p) :=
    Finset.sum_le_sum hpoint
  have hE₁ := sec7_sum_weight_le (box W) (fun _p : ℕ × ℕ × ℕ => (1 : ℝ))
    (A := L * A₁) (B := W ^ 7) hLA₁ h1
  have hE₂ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := L * F₁) (B := W ^ 13) hLF₁ hS
  have hE₃ := sec7_sum_weight_le (box W) (fun _p : ℕ × ℕ × ℕ => (1 : ℝ))
    (A := L * A₂) (B := W ^ 7) hLA₂ h1
  have hE₄ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := L * F₂) (B := W ^ 13) hLF₂ hS
  have hE₅ := sec7_sum_weight_le (box W) (fun _p : ℕ × ℕ × ℕ => (1 : ℝ))
    (A := L * A₃) (B := W ^ 7) hLA₃ h1
  have hE₆ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := L * F₃) (B := W ^ 13) hLF₃ hS
  have hE₇ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := L * A₄) (B := W ^ 13) hLA₄ hS
  have hE₈ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ 2)
    (A := L * F₄) (B := W ^ 19) hLF₄ hS2
  have hE₉ := sec7_sum_weight_le (box W) (fun _p : ℕ × ℕ × ℕ => (1 : ℝ))
    (A := L * A₅) (B := W ^ 7) hLA₅ h1
  have hE₁₀ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := L * F₅) (B := W ^ 13) hLF₅ hS
  have hE₁₁ := sec7_sum_weight_le (box W) (fun _p : ℕ × ℕ × ℕ => (1 : ℝ))
    (A := L * A₆) (B := W ^ 7) hLA₆ h1
  have hE₁₂ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := L * F₆) (B := W ^ 13) hLF₆ hS
  have hE₁₃ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((1:ℝ)/2))
    (A := L * 1) (B := W ^ 10) hL1 hSsqrtNat
  have hE₁₄ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((3:ℝ)/2))
    (A := L * F₇) (B := W ^ 16) hLF₇ hSthalfNat
  have hE₁₅ := sec7_sum_weight_le (box W) (fun _p : ℕ × ℕ × ℕ => (1 : ℝ))
    (A := L * 1) (B := W ^ 7) hL1 h1
  have hE₁₆ := sec7_sum_weight_le (box W)
    (fun p : ℕ × ℕ × ℕ => (Sbox p.1 p.2.1 p.2.2 : ℝ))
    (A := L * F₈) (B := W ^ 13) hLF₈ hS
  have hsum_bound :
      (∑ p ∈ box W, cnt p) ≤ sec7_cTriple * sec7_cBox * Z := by
    calc
      (∑ p ∈ box W, cnt p) ≤ (∑ p ∈ box W, sec7_cTriple * E p) := hsum0
      _ =
          (∑ p ∈ box W, sec7_cTriple * ((1 : ℝ) * (L * A₁)))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₁)))
        + (∑ p ∈ box W, sec7_cTriple * ((1 : ℝ) * (L * A₂)))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₂)))
        + (∑ p ∈ box W, sec7_cTriple * ((1 : ℝ) * (L * A₃)))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₃)))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * A₄)))
        + (∑ p ∈ box W, sec7_cTriple * (((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ 2) * (L * F₄)))
        + (∑ p ∈ box W, sec7_cTriple * ((1 : ℝ) * (L * A₅)))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₅)))
        + (∑ p ∈ box W, sec7_cTriple * ((1 : ℝ) * (L * A₆)))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₆)))
        + (∑ p ∈ box W, sec7_cTriple *
            (((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((1:ℝ)/2)) * (L * 1)))
        + (∑ p ∈ box W, sec7_cTriple *
            (((Sbox p.1 p.2.1 p.2.2 : ℝ) ^ ((3:ℝ)/2)) * (L * F₇)))
        + (∑ p ∈ box W, sec7_cTriple * ((1 : ℝ) * (L * 1)))
        + (∑ p ∈ box W, sec7_cTriple * ((Sbox p.1 p.2.1 p.2.2 : ℝ) * (L * F₈))) := by
          repeat rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          dsimp [E]
          ring
      _ ≤
          sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₁))
        + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₁))
        + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₂))
        + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₂))
        + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₃))
        + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₃))
        + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * A₄))
        + sec7_cTriple * sec7_cBox * (W ^ 19 * (L * F₄))
        + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₅))
        + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₅))
        + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₆))
        + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₆))
        + sec7_cTriple * sec7_cBox * (W ^ 10 * (L * 1))
        + sec7_cTriple * sec7_cBox * (W ^ 16 * (L * F₇))
        + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * 1))
        + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₈)) := by
          exact sec7_add16_le hE₁ hE₂ hE₃ hE₄ hE₅ hE₆ hE₇ hE₈
            hE₉ hE₁₀ hE₁₁ hE₁₂ hE₁₃ hE₁₄ hE₁₅ hE₁₆
      _ = sec7_cTriple * sec7_cBox * Z := by
          dsimp [Z]
          ring
  have hslice₁ : sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₁)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc1 Env hW hlog0 using 1
    dsimp [L, A₁]
    ring
  have hslice₂ : sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₁)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc5 Env hW hlog0 using 1
    dsimp [L, F₁, A₁]
    ring
  have hslice₃ : sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₂)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_n1 Env hW hlog0 using 1
    dsimp [L, A₂]
    ring
  have hslice₄ : sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₂)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_n2_fiber_z1 Env hW hlog0 using 1
    dsimp [L, F₂, A₂]
    ring
  have hslice₅ : sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₃)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_res1 Env hW hlog0 using 1
    dsimp [L, A₃]
    ring
  have hslice₆ : sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₃)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_res2 Env hW hlog0 using 1
    dsimp [L, F₃, A₃]
    ring
  have hslice₇ : sec7_cTriple * sec7_cBox * (W ^ 13 * (L * A₄)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_n2_sden Env hW hlog0 hG1 using 1
    dsimp [L, A₄]
    ring
  have hslice₈ : sec7_cTriple * sec7_cBox * (W ^ 19 * (L * F₄)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_n3 Env hW hlog0 using 1
    dsimp [L, F₄, A₄]
    ring
  have hslice₉ : sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₅)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc2 Env hW hlog0 using 1
    dsimp [L, A₅]
    ring
  have hslice₁₀ : sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₅)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc6 Env hW hlog0 using 1
    dsimp [L, F₅, A₅]
    ring
  have hslice₁₁ : sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₆)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc9 Env hW hlog0 using 1
    dsimp [L, A₆]
    ring
  have hslice₁₂ : sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₆)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc10 Env hW hlog0 using 1
    dsimp [L, F₆, A₆]
    ring
  have hslice₁₃ : sec7_cTriple * sec7_cBox * (W ^ 10 * (L * 1)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc3 Env hW hlog0 using 1
    dsimp [L]
    ring
  have hslice₁₄ : sec7_cTriple * sec7_cBox * (W ^ 16 * (L * F₇)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc7 Env hW hlog0 using 1
    dsimp [L, F₇]
    ring
  have hslice₁₅ : sec7_cTriple * sec7_cBox * (W ^ 7 * (L * 1)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc4 Env hW hlog0 using 1
    dsimp [L]
    ring
  have hslice₁₆ : sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₈)) ≤
      S.R / (18 * (W * sec7_harvM)) := by
    apply sec7_slice_of_fit hWpos
    convert sec7_nonzero_fit_tc8 Env hW hlog0 using 1
    dsimp [L, F₈]
    ring
  have hZ :
      sec7_cTriple * sec7_cBox * Z ≤ S.R / (W * sec7_harvM) := by
    let D : ℝ := S.R / (18 * (W * sec7_harvM))
    have hD0 : 0 ≤ D := by
      dsimp [D]
      exact div_nonneg (sec7_R_pos S).le
        (mul_nonneg (by norm_num) (mul_nonneg hWpos.le sec7_harvM_pos.le))
    have hsumSlices : sec7_cTriple * sec7_cBox * Z ≤ 16 * D := by
      calc
        sec7_cTriple * sec7_cBox * Z =
            sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₁))
          + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₁))
          + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₂))
          + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₂))
          + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₃))
          + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₃))
          + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * A₄))
          + sec7_cTriple * sec7_cBox * (W ^ 19 * (L * F₄))
          + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₅))
          + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₅))
          + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * A₆))
          + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₆))
          + sec7_cTriple * sec7_cBox * (W ^ 10 * (L * 1))
          + sec7_cTriple * sec7_cBox * (W ^ 16 * (L * F₇))
          + sec7_cTriple * sec7_cBox * (W ^ 7 * (L * 1))
          + sec7_cTriple * sec7_cBox * (W ^ 13 * (L * F₈)) := by
            dsimp [Z]
            ring
        _ ≤ D + D + D + D + D + D + D + D + D + D + D + D + D + D + D + D := by
            exact sec7_add16_le hslice₁ hslice₂ hslice₃ hslice₄ hslice₅ hslice₆
              hslice₇ hslice₈ hslice₉ hslice₁₀ hslice₁₁ hslice₁₂ hslice₁₃
              hslice₁₄ hslice₁₅ hslice₁₆
        _ = 16 * D := by ring
    calc
      sec7_cTriple * sec7_cBox * Z ≤ 16 * D := hsumSlices
      _ ≤ 18 * D := by linarith only [hD0]
      _ = S.R / (W * sec7_harvM) := by
        dsimp [D]
        field_simp [hWpos.ne', sec7_harvM_pos.ne']
  exact hsum_bound.trans hZ

end Squarefree
