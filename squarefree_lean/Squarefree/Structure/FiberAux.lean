import Squarefree.Structure.DaSpacing

/-!
# §3 helper lemmas for Proposition 3.2 (the `ℛ_a` fiber/approximation)

Self-contained algebraic / counting helpers used by `prop_3_2` in `Squarefree.Structure.Fiber`:
the closed form `R_a(d) = X a³/(d²(d+a)²)`, an algebraic mean-value lower bound on `|ΔR_a|`,
the near-integer property `R_a(d) ∈ ℤ + O(H/D)`, the gap-accumulation counting lemma
(writeup's "odd-indexed subsequence"), and the `rpow`-cube identities for the spacing
threshold and the `(Δ/A)^{8/3}G^{-2/3}` budget.  Factored out to keep `Fiber.lean` small.
-/

open Classical Finset

namespace Squarefree

/-- The closed-form value of Roth's quantity (sympy-verified, writeup line 334):
`R_a(d) = X a³ / (d²(d+a)²)`. -/
theorem Rfun_factor (X a d : ℝ) (hd : d ≠ 0) (hda : d + a ≠ 0) :
    Rfun X a d = X * a ^ 3 / (d ^ 2 * (d + a) ^ 2) := by
  unfold Rfun
  field_simp
  ring

/-- **Algebraic MVT lower bound** (replaces the writeup's `R_a' ≍ XA³/D⁵`, lines 373–377).
For `D ≤ d₁ < d_k ≤ 2D` and `0 < a ≤ D`,
`R_a(d₁) − R_a(d_k) ≥ (1/324)·X a³ (d_k − d₁)/D⁵`. -/
theorem Rfun_diff_lb (X a d₁ dk D : ℝ) (hX : 0 < X) (hD : 0 < D)
    (ha : 0 < a) (haD : a ≤ D)
    (h1lo : D ≤ d₁) (hlt : d₁ < dk) (hkhi : dk ≤ 2 * D) :
    (1 / 324 : ℝ) * X * a ^ 3 * (dk - d₁) / D ^ 5 ≤ Rfun X a d₁ - Rfun X a dk := by
  have hd1pos : 0 < d₁ := lt_of_lt_of_le hD h1lo
  have hdkpos : 0 < dk := lt_trans hd1pos hlt
  have hd1ne : d₁ ≠ 0 := ne_of_gt hd1pos
  have hd1ane : d₁ + a ≠ 0 := by positivity
  have hdkne : dk ≠ 0 := ne_of_gt hdkpos
  have hdkane : dk + a ≠ 0 := by positivity
  rw [Rfun_factor X a d₁ hd1ne hd1ane, Rfun_factor X a dk hdkne hdkane]
  set f1 : ℝ := d₁ ^ 2 * (d₁ + a) ^ 2 with hf1
  set fk : ℝ := dk ^ 2 * (dk + a) ^ 2 with hfk
  have hf1pos : 0 < f1 := by rw [hf1]; positivity
  have hfkpos : 0 < fk := by rw [hfk]; positivity
  have hD5pos : (0:ℝ) < D ^ 5 := by positivity
  have hprodpos : (0:ℝ) < f1 * fk := by positivity
  -- difference of the two reciprocal-products
  have hdiff : X * a ^ 3 / f1 - X * a ^ 3 / fk = X * a ^ 3 * (fk - f1) / (f1 * fk) := by
    rw [div_sub_div _ _ (ne_of_gt hf1pos) (ne_of_gt hfkpos),
      mul_comm f1 fk]
    congr 1
    ring
  rw [hdiff]
  rw [div_le_div_iff₀ hD5pos hprodpos]
  -- lower bound on (fk − f1):  fk − f1 ≥ 4 D³ (dk − d₁)
  have hflb : 4 * D ^ 3 * (dk - d₁) ≤ fk - f1 := by
    have hfact : fk - f1 = (dk - d₁) * (a + d₁ + dk) * (a * d₁ + a * dk + d₁ ^ 2 + dk ^ 2) := by
      rw [hf1, hfk]; ring
    rw [hfact]
    have hg1 : 2 * D ≤ a + d₁ + dk := by linarith
    have hkD : D ≤ dk := le_trans h1lo hlt.le
    have hg2 : 2 * D ^ 2 ≤ a * d₁ + a * dk + d₁ ^ 2 + dk ^ 2 := by
      have h1sq : D ^ 2 ≤ d₁ ^ 2 := by nlinarith only [h1lo, hD.le]
      have hksq : D ^ 2 ≤ dk ^ 2 := by nlinarith only [hkD, hD.le]
      have ha1 : (0:ℝ) ≤ a * d₁ := mul_nonneg ha.le hd1pos.le
      have hak : (0:ℝ) ≤ a * dk := mul_nonneg ha.le hdkpos.le
      linarith only [h1sq, hksq, ha1, hak]
    have hdpos : (0:ℝ) ≤ dk - d₁ := by linarith
    have hp1 : (0:ℝ) ≤ a + d₁ + dk := by positivity
    calc 4 * D ^ 3 * (dk - d₁)
        = (dk - d₁) * (2 * D * (2 * D ^ 2)) := by ring
      _ ≤ (dk - d₁) * ((a + d₁ + dk) * (a * d₁ + a * dk + d₁ ^ 2 + dk ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hg1 hg2 (by positivity) hp1) hdpos
      _ = (dk - d₁) * (a + d₁ + dk) * (a * d₁ + a * dk + d₁ ^ 2 + dk ^ 2) := by ring
  -- upper bound on (f1 · fk):  f1 · fk ≤ 1296 D⁸  (uses a ≤ D, d ≤ 2D)
  have hf1ub : f1 ≤ 36 * D ^ 4 := by
    have h1 : d₁ ^ 2 ≤ 4 * D ^ 2 := by nlinarith only [h1lo, hlt.le, hkhi, hd1pos.le]
    have h2 : (d₁ + a) ^ 2 ≤ 9 * D ^ 2 := by
      have hle : d₁ + a ≤ 3 * D := by linarith
      have hge : (0:ℝ) ≤ d₁ + a := by positivity
      nlinarith only [hle, hge]
    rw [hf1]
    calc d₁ ^ 2 * (d₁ + a) ^ 2 ≤ (4 * D ^ 2) * (9 * D ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 36 * D ^ 4 := by ring
  have hfkub : fk ≤ 36 * D ^ 4 := by
    have h1 : dk ^ 2 ≤ 4 * D ^ 2 := by nlinarith only [hkhi, hdkpos.le]
    have h2 : (dk + a) ^ 2 ≤ 9 * D ^ 2 := by
      have hle : dk + a ≤ 3 * D := by linarith
      have hge : (0:ℝ) ≤ dk + a := by positivity
      nlinarith only [hle, hge]
    rw [hfk]
    calc dk ^ 2 * (dk + a) ^ 2 ≤ (4 * D ^ 2) * (9 * D ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 36 * D ^ 4 := by ring
  have hfprod : f1 * fk ≤ 1296 * D ^ 8 := by
    calc f1 * fk ≤ (36 * D ^ 4) * (36 * D ^ 4) :=
          mul_le_mul hf1ub hfkub hfkpos.le (by positivity)
      _ = 1296 * D ^ 8 := by ring
  -- assemble
  have hXa3 : (0:ℝ) ≤ X * a ^ 3 := by positivity
  have hdkd1 : (0:ℝ) ≤ dk - d₁ := by linarith
  calc (1 / 324 : ℝ) * X * a ^ 3 * (dk - d₁) * (f1 * fk)
      ≤ (1 / 324 : ℝ) * X * a ^ 3 * (dk - d₁) * (1296 * D ^ 8) := by
        apply mul_le_mul_of_nonneg_left hfprod (by positivity)
    _ = X * a ^ 3 * (4 * D ^ 3 * (dk - d₁)) * D ^ 5 := by ring
    _ ≤ X * a ^ 3 * (fk - f1) * D ^ 5 := by
        apply mul_le_mul_of_nonneg_right _ hD5pos.le
        exact mul_le_mul_of_nonneg_left hflb hXa3

/-- Cube of the regime bound on `a`:  `a ≥ 64 Δ^{4/3}(H⁴/X)^{1/3}  ⇒  a³ ≥ 64³ Δ⁴ H⁴/X`. -/
theorem a_cubed_lb (X H Δ a : ℝ) (hX : 0 < X) (hΔ : 0 < Δ) (_ha : 0 < a)
    (ha_lo : (64 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ) ≤ a) :
    (262144 : ℝ) * Δ ^ (4:ℕ) * (H ^ 4 / X) ≤ a ^ 3 := by
  have hcube : ((64 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ)) ^ 3
      = (262144 : ℝ) * Δ ^ (4 : ℕ) * (H ^ 4 / X) := by
    have e2 : (Δ ^ (4/3 : ℝ)) ^ (3:ℕ) = Δ ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast (Δ ^ (4/3 : ℝ)) 3, ← Real.rpow_mul hΔ.le]
      rw [show (4/3 : ℝ) * (3:ℕ) = (4 : ℕ) by push_cast; ring, Real.rpow_natCast]
    have hHX : (0:ℝ) ≤ H ^ 4 / X := by positivity
    have e3 : ((H ^ 4 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) = H ^ 4 / X := by
      rw [← Real.rpow_natCast ((H ^ 4 / X) ^ (1/3 : ℝ)) 3,
        ← Real.rpow_mul hHX]; norm_num
    calc ((64 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ)) ^ 3
        = (64:ℝ) ^ 3 * (Δ ^ (4/3 : ℝ)) ^ (3:ℕ) * ((H ^ 4 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) := by ring
      _ = (262144 : ℝ) * Δ ^ (4 : ℕ) * (H ^ 4 / X) := by rw [e2, e3]; norm_num
  rw [← hcube]
  have hb : (0:ℝ) ≤ (64 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ) := by
    have h1 : (0:ℝ) ≤ Δ ^ (4/3 : ℝ) := (Real.rpow_pos_of_pos hΔ _).le
    have h2 : (0:ℝ) ≤ (H ^ 4 / X) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
    positivity
  gcongr

/-- Lowered-threshold (`λ = 1/4`) cube bound with a `Δ`-floor.

From `a ≥ (1/4)·Δ^{4/3}(H⁴/X)^{1/3}` we only get `a³ ≥ (1/64)·Δ⁴·H⁴/X`; trading one power of
`Δ` against the floor `Δ ≥ 2²⁴` recovers the same `262144·Δ³·(H⁴/X) ≤ a³` shape the fiber
proofs consume (now with `Δ³` rather than `Δ⁴`).  Used by `prop_3_2_fiber(_dStar)`. -/
theorem a_cubed_lb_quarter (X H Δ a : ℝ) (hX : 0 < X) (hΔ : 0 < Δ) (_ha : 0 < a)
    (hΔlb : (16777216 : ℝ) ≤ Δ)
    (ha_lo : (1/4 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ) ≤ a) :
    (262144 : ℝ) * Δ ^ (3:ℕ) * (H ^ 4 / X) ≤ a ^ 3 := by
  -- first the genuine `(1/64) Δ⁴ (H⁴/X) ≤ a³`
  have hcube : ((1/4 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ)) ^ 3
      = (1/64 : ℝ) * Δ ^ (4 : ℕ) * (H ^ 4 / X) := by
    have e2 : (Δ ^ (4/3 : ℝ)) ^ (3:ℕ) = Δ ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast (Δ ^ (4/3 : ℝ)) 3, ← Real.rpow_mul hΔ.le]
      rw [show (4/3 : ℝ) * (3:ℕ) = (4 : ℕ) by push_cast; ring, Real.rpow_natCast]
    have hHX : (0:ℝ) ≤ H ^ 4 / X := by positivity
    have e3 : ((H ^ 4 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) = H ^ 4 / X := by
      rw [← Real.rpow_natCast ((H ^ 4 / X) ^ (1/3 : ℝ)) 3,
        ← Real.rpow_mul hHX]; norm_num
    calc ((1/4 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ)) ^ 3
        = (1/4:ℝ) ^ 3 * (Δ ^ (4/3 : ℝ)) ^ (3:ℕ) * ((H ^ 4 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) := by ring
      _ = (1/64 : ℝ) * Δ ^ (4 : ℕ) * (H ^ 4 / X) := by rw [e2, e3]; norm_num
  have hquarter : (1/64 : ℝ) * Δ ^ (4 : ℕ) * (H ^ 4 / X) ≤ a ^ 3 := by
    rw [← hcube]
    have hb : (0:ℝ) ≤ (1/4 : ℝ) * Δ ^ (4/3 : ℝ) * (H ^ 4 / X) ^ (1/3 : ℝ) := by
      have h1 : (0:ℝ) ≤ Δ ^ (4/3 : ℝ) := (Real.rpow_pos_of_pos hΔ _).le
      have h2 : (0:ℝ) ≤ (H ^ 4 / X) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
      positivity
    gcongr
  -- trade a power of Δ: (1/64) Δ⁴ ≥ 262144 Δ³ ⇔ Δ ≥ 2²⁴
  have hHXpos : (0:ℝ) ≤ H ^ 4 / X := by positivity
  have hΔ3pos : (0:ℝ) < Δ ^ (3:ℕ) := by positivity
  have htrade : (262144 : ℝ) * Δ ^ (3:ℕ) * (H ^ 4 / X) ≤ (1/64 : ℝ) * Δ ^ (4 : ℕ) * (H ^ 4 / X) := by
    have hΔ4 : Δ ^ (4:ℕ) = Δ ^ (3:ℕ) * Δ := by ring
    rw [hΔ4]
    have hstep : (262144 : ℝ) * Δ ^ (3:ℕ) ≤ (1/64 : ℝ) * (Δ ^ (3:ℕ) * Δ) := by
      nlinarith only [hΔ3pos, hΔlb]
    nlinarith only [mul_le_mul_of_nonneg_right hstep hHXpos]
  linarith [htrade, hquarter]

/-- The spacing threshold `spc := (1/10) a^{-1/3} Δ^{5/3}(H⁵/X)^{1/3}` is positive with
cube `(1/1000) Δ⁵(H⁵/X)/a`. -/
theorem spc_pos_cube (X H Δ a : ℝ) (hX : 0 < X) (hH : 0 < H) (hΔ : 0 < Δ) (ha : 0 < a) :
    0 < (1/10 : ℝ) * a ^ (-1/3 : ℝ) * Δ ^ (5/3 : ℝ) * (H ^ 5 / X) ^ (1/3 : ℝ) ∧
    ((1/10 : ℝ) * a ^ (-1/3 : ℝ) * Δ ^ (5/3 : ℝ) * (H ^ 5 / X) ^ (1/3 : ℝ)) ^ 3
      = (1/1000 : ℝ) * Δ ^ (5:ℕ) * (H ^ 5 / X) / a := by
  have hHX : (0:ℝ) ≤ H ^ 5 / X := by positivity
  constructor
  · have h1 : (0:ℝ) < a ^ (-1/3 : ℝ) := Real.rpow_pos_of_pos ha _
    have h2 : (0:ℝ) < Δ ^ (5/3 : ℝ) := Real.rpow_pos_of_pos hΔ _
    have h3 : (0:ℝ) ≤ (H ^ 5 / X) ^ (1/3 : ℝ) := Real.rpow_nonneg hHX _
    positivity
  · have e1 : (a ^ (-1/3 : ℝ)) ^ (3:ℕ) = a⁻¹ := by
      rw [← Real.rpow_natCast (a ^ (-1/3 : ℝ)) 3, ← Real.rpow_mul ha.le]
      rw [show (-1/3 : ℝ) * (3:ℕ) = (-1 : ℝ) by push_cast; ring, Real.rpow_neg_one]
    have e2 : (Δ ^ (5/3 : ℝ)) ^ (3:ℕ) = Δ ^ (5 : ℕ) := by
      rw [← Real.rpow_natCast (Δ ^ (5/3 : ℝ)) 3, ← Real.rpow_mul hΔ.le]
      rw [show (5/3 : ℝ) * (3:ℕ) = (5 : ℕ) by push_cast; ring, Real.rpow_natCast]
    have e3 : ((H ^ 5 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) = H ^ 5 / X := by
      rw [← Real.rpow_natCast ((H ^ 5 / X) ^ (1/3 : ℝ)) 3, ← Real.rpow_mul hHX]; norm_num
    have hpow : ((1/10 : ℝ) * a ^ (-1/3 : ℝ) * Δ ^ (5/3 : ℝ) * (H ^ 5 / X) ^ (1/3 : ℝ)) ^ 3
        = (1/10 : ℝ) ^ 3 * (a ^ (-1/3 : ℝ)) ^ (3:ℕ) * (Δ ^ (5/3 : ℝ)) ^ (3:ℕ)
          * ((H ^ 5 / X) ^ (1/3 : ℝ)) ^ (3:ℕ) := by ring
    rw [hpow, e1, e2, e3]
    field_simp
    ring

/-- The `(Δ/A)^{8/3} G^{-2/3}` budget is positive with cube `Δ⁸/(A⁸ G²)`. -/
theorem target_pos_cube (Δ A G : ℝ) (hΔ : 0 < Δ) (hA : 0 < A) (hG : 0 < G) :
    0 < (Δ / A) ^ (8/3 : ℝ) * G ^ (-2/3 : ℝ) ∧
    ((Δ / A) ^ (8/3 : ℝ) * G ^ (-2/3 : ℝ)) ^ 3 = Δ ^ (8:ℕ) / (A ^ (8:ℕ) * G ^ (2:ℕ)) := by
  have hpos : 0 < (Δ / A) ^ (8/3 : ℝ) * G ^ (-2/3 : ℝ) := by
    have h1 : (0:ℝ) < (Δ / A) ^ (8/3 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    have h2 : (0:ℝ) < G ^ (-2/3 : ℝ) := Real.rpow_pos_of_pos hG _
    positivity
  refine ⟨hpos, ?_⟩
  have e1 : ((Δ / A) ^ (8/3 : ℝ)) ^ (3:ℕ) = (Δ / A) ^ (8:ℕ) := by
    rw [← Real.rpow_natCast ((Δ / A) ^ (8/3 : ℝ)) 3, ← Real.rpow_mul (by positivity)]
    rw [show (8/3 : ℝ) * (3:ℕ) = (8 : ℕ) by push_cast; ring, Real.rpow_natCast]
  have e2 : (G ^ (-2/3 : ℝ)) ^ (3:ℕ) = G⁻¹ ^ (2:ℕ) := by
    rw [← Real.rpow_natCast (G ^ (-2/3 : ℝ)) 3, ← Real.rpow_mul hG.le]
    rw [show (-2/3 : ℝ) * (3:ℕ) = ((-2 : ℤ):ℝ) by push_cast; ring, Real.rpow_intCast]
    rw [zpow_neg, ← inv_zpow]; norm_cast
  have hpow : ((Δ / A) ^ (8/3 : ℝ) * G ^ (-2/3 : ℝ)) ^ 3
      = ((Δ / A) ^ (8/3 : ℝ)) ^ (3:ℕ) * (G ^ (-2/3 : ℝ)) ^ (3:ℕ) := by ring
  rw [hpow, e1, e2]
  rw [div_pow]
  field_simp

/-- **Gap-accumulation counting** (writeup line 369–381, the "odd-indexed subsequence").
A finite set `T ⊂ ℤ` such that any two elements with a third strictly between them are
spaced `≥ spc`, and whose total spread is `≤ W`, has `#T ≤ 2 + 2 W / spc`. -/
theorem gap_card_bound (T : Finset ℤ) (spc W : ℝ) (hspc : 0 < spc) (hW : 0 ≤ W)
    (hgap : ∀ d d'' : ℤ, d ∈ T → d'' ∈ T → d < d'' → (∃ d' ∈ T, d < d' ∧ d' < d'') →
      spc ≤ (d'' : ℝ) - (d : ℝ))
    (hspread : ∀ d d'' : ℤ, d ∈ T → d'' ∈ T → (d'' : ℝ) - (d : ℝ) ≤ W) :
    (T.card : ℝ) ≤ 2 + 2 * W / spc := by
  set k := T.card with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0]
    have : (0:ℝ) ≤ 2 * W / spc := by positivity
    push_cast; linarith
  -- enumerate T monotonically
  set e := T.orderEmbOfFin hk.symm with hedef
  have hmem : ∀ i : Fin k, e i ∈ T := fun i => T.orderEmbOfFin_mem hk.symm i
  have hmono : StrictMono e := (T.orderEmbOfFin hk.symm).strictMono
  -- key: for 2j ≤ k-1,  spc * j ≤ e⟨2j⟩ - e⟨0⟩
  have hstep : ∀ j : ℕ, (h2j : 2 * j < k) →
      spc * (j : ℝ) ≤ (e ⟨2 * j, h2j⟩ : ℝ) - (e ⟨0, hkpos⟩ : ℝ) := by
    intro j
    induction j with
    | zero => intro h2j; simp
    | succ n ih =>
      intro h2j
      have h2n : 2 * n < k := by omega
      have h2n1 : 2 * n + 1 < k := by omega
      -- gap between e⟨2n⟩ and e⟨2n+2⟩ ≥ spc (e⟨2n+1⟩ strictly between, in T)
      have hidx : (⟨2 * n, h2n⟩ : Fin k) < ⟨2 * n + 1, h2n1⟩ := by
        simp [Fin.lt_def]
      have hidx2 : (⟨2 * n + 1, h2n1⟩ : Fin k) < ⟨2 * (n + 1), h2j⟩ := by
        simp only [Fin.lt_def]; omega
      have hlt1 : e ⟨2 * n, h2n⟩ < e ⟨2 * n + 1, h2n1⟩ := hmono hidx
      have hlt2 : e ⟨2 * n + 1, h2n1⟩ < e ⟨2 * (n + 1), h2j⟩ := hmono hidx2
      have hgapn : spc ≤ (e ⟨2 * (n + 1), h2j⟩ : ℝ) - (e ⟨2 * n, h2n⟩ : ℝ) :=
        hgap _ _ (hmem _) (hmem _) (by exact_mod_cast lt_trans hlt1 hlt2)
          ⟨e ⟨2 * n + 1, h2n1⟩, hmem _, hlt1, hlt2⟩
      have := ih h2n
      push_cast
      push_cast at this
      linarith
  -- pick j = (k-1)/2
  set j₀ := (k - 1) / 2 with hj0
  have h2j0 : 2 * j₀ < k := by omega
  have hjle : (k : ℝ) - 2 ≤ 2 * (j₀ : ℝ) := by
    have : (k - 1) ≤ 2 * j₀ + 1 := by omega
    have hck : ((k:ℤ):ℝ) = (k:ℝ) := by norm_cast
    have : (k : ℝ) ≤ 2 * (j₀ : ℝ) + 2 := by
      have hh : (k - 1 : ℕ) ≤ 2 * j₀ + 1 := by omega
      have := (Nat.cast_le (α := ℝ)).mpr hh
      push_cast at this
      have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
      have : ((k:ℝ) - 1) ≤ 2 * (j₀:ℝ) + 1 := by
        have hcast : ((k - 1 : ℕ) : ℝ) = (k:ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; norm_num
        rw [hcast] at this; exact this
      linarith
    linarith
  have hacc := hstep j₀ h2j0
  have hspread' : (e ⟨2 * j₀, h2j0⟩ : ℝ) - (e ⟨0, hkpos⟩ : ℝ) ≤ W :=
    hspread _ _ (hmem _) (hmem _)
  -- spc * j₀ ≤ W  ⇒  j₀ ≤ W/spc  ⇒  k ≤ 2 + 2 W/spc
  have hsj0 : spc * (j₀ : ℝ) ≤ W := le_trans hacc hspread'
  have hj0le : (j₀ : ℝ) ≤ W / spc := by
    rw [le_div_iff₀ hspc]; linarith [hsj0]
  have : (k : ℝ) ≤ 2 + 2 * (j₀ : ℝ) := by linarith [hjle]
  calc (k : ℝ) ≤ 2 + 2 * (j₀ : ℝ) := this
    _ ≤ 2 + 2 * (W / spc) := by linarith [hj0le]
    _ = 2 + 2 * W / spc := by ring

/-- Symmetric (absolute-value) form of `Rfun_diff_lb`, for the Newton-step bound. -/
theorem Rfun_diff_lb_abs (X a d₁ d₂ D : ℝ) (hX : 0 < X) (hD : 0 < D)
    (ha : 0 < a) (haD : a ≤ D)
    (h1lo : D ≤ d₁) (h1hi : d₁ ≤ 2 * D) (h2lo : D ≤ d₂) (h2hi : d₂ ≤ 2 * D) :
    (1 / 324 : ℝ) * X * a ^ 3 * |d₁ - d₂| / D ^ 5 ≤ |Rfun X a d₁ - Rfun X a d₂| := by
  have hD5pos : (0:ℝ) < D ^ 5 := by positivity
  rcases lt_trichotomy d₁ d₂ with h | h | h
  · -- d₁ < d₂ :  Rfun(d₁) ≥ Rfun(d₂),  |d₁−d₂| = d₂−d₁
    have key := Rfun_diff_lb X a d₁ d₂ D hX hD ha haD h1lo h h2hi
    have hnn : (0:ℝ) ≤ (1 / 324 : ℝ) * X * a ^ 3 * (d₂ - d₁) / D ^ 5 := by
      have : (0:ℝ) ≤ d₂ - d₁ := by linarith
      apply div_nonneg _ hD5pos.le
      have h3 : (0:ℝ) ≤ a ^ 3 := by positivity
      have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/324) hX.le) h3) this
      linarith [this]
    rw [abs_of_nonpos (by linarith : d₁ - d₂ ≤ 0),
      abs_of_nonneg (by linarith [key, hnn] : (0:ℝ) ≤ Rfun X a d₁ - Rfun X a d₂)]
    have heq : (1 / 324 : ℝ) * X * a ^ 3 * -(d₁ - d₂) / D ^ 5
        = (1 / 324 : ℝ) * X * a ^ 3 * (d₂ - d₁) / D ^ 5 := by ring
    rw [heq]; exact key
  · subst h; simp
  · -- d₂ < d₁ :  Rfun(d₂) ≥ Rfun(d₁),  |d₁−d₂| = d₁−d₂
    have key := Rfun_diff_lb X a d₂ d₁ D hX hD ha haD h2lo h h1hi
    have hnn : (0:ℝ) ≤ (1 / 324 : ℝ) * X * a ^ 3 * (d₁ - d₂) / D ^ 5 := by
      have : (0:ℝ) ≤ d₁ - d₂ := by linarith
      apply div_nonneg _ hD5pos.le
      have h3 : (0:ℝ) ≤ a ^ 3 := by positivity
      have := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/324) hX.le) h3) this
      linarith [this]
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ d₁ - d₂),
      abs_of_nonpos (by linarith [key, hnn] : Rfun X a d₁ - Rfun X a d₂ ≤ 0)]
    have heq : -(Rfun X a d₁ - Rfun X a d₂) = Rfun X a d₂ - Rfun X a d₁ := by ring
    rw [heq]; linarith [key]

/-- **Near-integer property** (writeup line 363): `R_a(d) = (integer) + O(H/D)`.
With `D ≤ d ≤ 2D`, `0 < a ≤ D`, there is `J ∈ ℤ` with `|R_a(d) − J| ≤ 14·H/D`. -/
theorem Rfun_near_int (X H a d D : ℝ) (_hX : 0 < X) (hH : 0 < H) (hD : 0 < D)
    (ha : 0 < a) (haD : a ≤ D) (hd_lo : D ≤ d) (hd_hi : d ≤ 2 * D)
    (m₁ m₂ : ℤ)
    (he1 : 0 ≤ (m₁:ℝ) - X / d ^ 2) (he1' : (m₁:ℝ) - X / d ^ 2 ≤ H / d ^ 2)
    (he2 : 0 ≤ (m₂:ℝ) - X / (d + a) ^ 2) (he2' : (m₂:ℝ) - X / (d + a) ^ 2 ≤ H / (d + a) ^ 2)
    (n : ℤ) (hn : (n:ℝ) = -(2 * d - a) * (m₁:ℝ) + (2 * d + 3 * a) * (m₂:ℝ)) :
    |Rfun X a d - (n:ℝ)| ≤ 14 * H / D := by
  have hdpos : 0 < d := lt_of_lt_of_le hD hd_lo
  have hdapos : 0 < d + a := by linarith
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hda2 : (0:ℝ) < (d + a) ^ 2 := by positivity
  set e1 : ℝ := (m₁:ℝ) - X / d ^ 2 with he1def
  set e2 : ℝ := (m₂:ℝ) - X / (d + a) ^ 2 with he2def
  have hm1 : (m₁:ℝ) = X / d ^ 2 + e1 := by rw [he1def]; ring
  have hm2 : (m₂:ℝ) = X / (d + a) ^ 2 + e2 := by rw [he2def]; ring
  -- R_a(d) − n  =  (2d−a) e1 − (2d+3a) e2
  have hkey : Rfun X a d - (n:ℝ) = (2 * d - a) * e1 - (2 * d + 3 * a) * e2 := by
    unfold Rfun
    rw [hn, hm1, hm2]; ring
  rw [hkey]
  -- coefficient bounds:  0 ≤ 2d−a ≤ 4D,  0 ≤ 2d+3a ≤ 10D
  have hc1_lo : 0 ≤ 2 * d - a := by linarith
  have hc1_hi : 2 * d - a ≤ 4 * D := by linarith
  have hc2_lo : 0 ≤ 2 * d + 3 * a := by linarith
  have hc2_hi : 2 * d + 3 * a ≤ 10 * D := by linarith
  -- e bounds vs H/D²:  H/d² ≤ H/D², H/(d+a)² ≤ H/D²
  have hD2 : (0:ℝ) < D ^ 2 := by positivity
  have hHd : H / d ^ 2 ≤ H / D ^ 2 :=
    div_le_div_of_nonneg_left hH.le hD2 (by nlinarith only [hd_lo, hD.le])
  have hHda : H / (d + a) ^ 2 ≤ H / D ^ 2 :=
    div_le_div_of_nonneg_left hH.le hD2 (by nlinarith only [hd_lo, ha.le, hD.le])
  have he1'' : e1 ≤ H / D ^ 2 := le_trans he1' hHd
  have he2'' : e2 ≤ H / D ^ 2 := le_trans he2' hHda
  have hHDnn : (0:ℝ) ≤ H / D ^ 2 := by positivity
  -- bound the two products
  have hDne : D ≠ 0 := ne_of_gt hD
  have e4 : 4 * D * (H / D ^ 2) = 4 * H / D := by field_simp
  have e10 : 10 * D * (H / D ^ 2) = 10 * H / D := by field_simp
  have t1 : (2 * d - a) * e1 ≤ 4 * H / D := by
    rw [← e4]; exact mul_le_mul hc1_hi he1'' he1 (by linarith)
  have t2 : (2 * d + 3 * a) * e2 ≤ 10 * H / D := by
    rw [← e10]; exact mul_le_mul hc2_hi he2'' he2 (by linarith)
  have t1' : 0 ≤ (2 * d - a) * e1 := mul_nonneg hc1_lo he1
  have t2' : 0 ≤ (2 * d + 3 * a) * e2 := mul_nonneg hc2_lo he2
  have hub : (2 * d - a) * e1 - (2 * d + 3 * a) * e2 ≤ 14 * H / D := by
    have : (14:ℝ) * H / D = 4 * H / D + 10 * H / D := by ring
    linarith [t1, t2']
  have hlb : -(14 * H / D) ≤ (2 * d - a) * e1 - (2 * d + 3 * a) * e2 := by
    have : -(14 * H / D) = -(4 * H / D) - 10 * H / D := by ring
    linarith [t1', t2]
  rw [abs_le]; exact ⟨hlb, hub⟩

end Squarefree
