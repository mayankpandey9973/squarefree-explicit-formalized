import Squarefree.Structure.FiberAux

/-!
# Proposition 3.2 — the `ℛ_a` fiber/approximation (layer L2)

For each `a ∼ A` there is a set `ℛ_a` (with `r ≍ R`) and a map `d_a^* : ℛ_a → 𝒟_a` with the
(stated weak, non-sharp) fiber bound `#𝒟_a/#ℛ_a ≪ 1 + (Δ/A)^{8/3} G^{-2/3}` and the
approximation `d_a^*(r) = d̃_a(r) + O((Δ/G)(Δ³/A³))`, where `d̃_a = R_a⁻¹`.

Faithful to `explicit_writeup.md` lines 346–393; uses `lemma_3_1` (so it carries the same
regime hypotheses).  `d̃_a` (here `dtil`) is supplied as a right-inverse of `R_a` on the band
`[c₁R, C₁R]` — a HYPOTHESIS, not a conclusion (the original stub had it as a conclusion under
`∀ dtil`, which is false: an arbitrary `dtil` forces `Ra = ∅` and then the `DaCard` clause fails).

Two faithful regime hypotheses are threaded (matching the writeup's "fix such a dyadic scale `A`"
and "`[D,2D]` with `D = HΔ`"): `D = S.D` and `a ∼ A` (`S.A ≤ a ≤ 2 S.A`).  Algebraic helpers live
in `Squarefree.Structure.FiberAux`.
-/

open Classical Finset

namespace Squarefree

set_option maxHeartbeats 1600000 in
/-- **Prop 3.2** (writeup 346–393).  Fiber bound is the STATED WEAK (non-sharp) form.

Threaded faithful regime hypotheses (beyond `lemma_3_1`'s): the dyadic window `D = S.D`
(writeup `D = HΔ`); the fixed dyadic scale `a ∼ A` (`S.A ≤ a ≤ 2 S.A`); the pigeonhole
upper limit `2A ≤ D` (writeup `A ≪ ΔU ≪ D`); and the localization of the inverse
`d̃_a(ρ) ∈ [D, 2D]` (writeup line 343, `d̃_a ≍ HΔ = D`). -/
theorem prop_3_2 : ∃ (c₁ C₁ C₂ C₃ : ℝ), 0 < c₁ ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ), 0 < a →
      P.X ^ (1/100 : ℝ) ≤ S.Δ →
      (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
      (1/4 : ℝ) * S.Δ ^ (4/3 : ℝ) * (P.H ^ 4 / P.X) ^ (1/3 : ℝ) ≤ (a : ℝ) →
      S.A ≤ (a : ℝ) → (a : ℝ) ≤ 2 * S.A → 2 * S.A ≤ S.D →
      ∀ (D : ℝ), 0 < D → D = S.D → ∀ (dtil : ℝ → ℝ),
        (∀ ρ : ℝ, c₁ * S.R ≤ ρ → ρ ≤ C₁ * S.R →
          Rfun P.X (a : ℝ) (dtil ρ) = ρ ∧ S.D ≤ dtil ρ ∧ dtil ρ ≤ 2 * S.D) →
        ∃ (Ra : Finset ℕ) (dStar : ℕ → ℤ),
          (∀ r ∈ Ra, inDa P.X P.H a (dStar r)) ∧
          (∀ r ∈ Ra, c₁ * S.R ≤ (r : ℝ) ∧ (r : ℝ) ≤ C₁ * S.R) ∧
          ((DaCard P.X P.H a D : ℝ) ≤
            C₂ * (Ra.card : ℝ) * (1 + (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ))) ∧
          (∀ r ∈ Ra, |(dStar r : ℝ) - dtil (r : ℝ)| ≤ C₃ * (S.Δ / P.G) * (S.Δ ^ 3 / S.A ^ 3)) := by
  obtain ⟨c, hc_pos, hc⟩ := lemma_3_1
  refine ⟨1/72, 16, 18144 / c + 2, 4536, by norm_num, by norm_num, by positivity, by norm_num, ?_⟩
  intro P S a ha hΔlo hX0 ha_lo hAa haA hAD D hDpos hDeq dtil hdtil
  have hΔ : (16777216 : ℝ) ≤ S.Δ := le_trans hX0 hΔlo
  -- basic positivity (no `set`, to keep scale identities literal)
  have hXpos : 0 < P.X := P.X_pos
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDSeq : S.D = P.H * S.Δ := rfl
  have hDSpos : 0 < S.D := by rw [hDSeq]; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have haRpos : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  -- a ≤ D = S.D  (from a ≤ 2A ≤ D)
  have haD : (a:ℝ) ≤ D := by rw [hDeq]; linarith [haA, hAD]
  -- R = X A³ / S.D⁴
  have hRval : S.R = P.X * S.A ^ 3 / S.D ^ 4 := by
    rw [S.R_eq_orig, hDSeq]
    rw [show (P.H * S.Δ) ^ 4 = S.Δ ^ 4 * P.H ^ 4 by ring]
  -- lowered threshold: a³ ≥ 262144 Δ³ H⁴/X (one power of Δ traded against the floor Δ ≥ 2²⁴)
  have ha3 : (262144 : ℝ) * S.Δ ^ (3:ℕ) * (P.H ^ 4 / P.X) ≤ (a:ℝ) ^ 3 :=
    a_cubed_lb_quarter P.X P.H S.Δ a hXpos hΔpos haRpos (by linarith [hΔ]) ha_lo
  -- with the lowered threshold the band lower bound degrades to `R ≥ 32768/Δ`
  have hRlb : (32768 : ℝ) / S.Δ ≤ S.R := by
    have hAge : (a:ℝ) / 2 ≤ S.A := by linarith [haA]
    have hAcube : ((a:ℝ) / 2) ^ 3 ≤ S.A ^ 3 := pow_le_pow_left₀ (by positivity) hAge 3
    have hD4 : S.D ^ 4 = S.Δ ^ (4:ℕ) * P.H ^ 4 := by rw [hDSeq]; ring
    have hD4pos : (0:ℝ) < S.D ^ 4 := by positivity
    rw [hRval, div_le_div_iff₀ hΔpos hD4pos, hD4]
    have haX : (262144 : ℝ) * S.Δ ^ (3:ℕ) * P.H ^ 4 ≤ (a:ℝ) ^ 3 * P.X := by
      have e : (262144 : ℝ) * S.Δ ^ (3:ℕ) * (P.H ^ 4 / P.X) * P.X
          = 262144 * S.Δ ^ (3:ℕ) * P.H ^ 4 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right ha3 hXpos.le, e]
    have hPXA : P.X * ((a:ℝ)/2) ^ 3 ≤ P.X * S.A ^ 3 :=
      mul_le_mul_of_nonneg_left hAcube hXpos.le
    have hΔ4 : S.Δ ^ (4:ℕ) = S.Δ ^ (3:ℕ) * S.Δ := by ring
    rw [hΔ4]
    nlinarith [haX, hPXA, hXpos.le, mul_le_mul_of_nonneg_right haX hΔpos.le,
      mul_pos hΔpos (pow_pos hΔpos 3)]
  -- chosen near-integer for a 𝒟-element
  have hd2pos : ∀ d : ℤ, (0:ℝ) < S.D → S.D ≤ (d:ℝ) → (0:ℝ) < (d:ℝ) ^ 2 := by
    intro d hD hle; have : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hD hle; positivity
  classical
  -- `getm d` : an integer with 0 ≤ getm d − X/d² ≤ H/d² when d ∈ 𝒟 (else junk)
  set getm : ℤ → ℤ := fun d =>
    if h : (∃ m : ℤ, P.X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ P.X + P.H)
      then h.choose else 0 with hgetm
  have hgetm_spec : ∀ d : ℤ, (0:ℝ) < (d:ℝ) ^ 2 → inD P.X P.H d →
      0 ≤ (getm d : ℝ) - P.X / (d:ℝ) ^ 2 ∧ (getm d : ℝ) - P.X / (d:ℝ) ^ 2 ≤ P.H / (d:ℝ) ^ 2 := by
    intro d hd2 hin
    have hex : (∃ m : ℤ, P.X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ P.X + P.H) := hin
    have hval : getm d = hex.choose := by rw [hgetm]; simp only [hex, dif_pos]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    rw [hval]
    have hne : (d:ℝ) ^ 2 ≠ 0 := ne_of_gt hd2
    have key : ((hex.choose:ℝ) - P.X / (d:ℝ) ^ 2) * (d:ℝ) ^ 2 = (hex.choose:ℝ) * (d:ℝ) ^ 2 - P.X := by
      rw [sub_mul, div_mul_cancel₀ P.X hne]
    constructor
    · have h0 : 0 ≤ ((hex.choose:ℝ) - P.X / (d:ℝ) ^ 2) * (d:ℝ) ^ 2 := by rw [key]; linarith
      exact (mul_nonneg_iff_of_pos_right hd2).mp h0
    · rw [le_div_iff₀ hd2, key]; linarith
  -- `rStar d` : Roth's integer near R_a(d)
  set rStar : ℤ → ℤ := fun d =>
    -(2 * d - a) * getm d + (2 * d + 3 * a) * getm (d + a) with hrStar
  -- near-integer property for d ∈ 𝒟_a ∩ [D,2D]
  have hnear : ∀ d : ℤ, inDa P.X P.H a d → S.D ≤ (d:ℝ) → (d:ℝ) ≤ 2 * S.D →
      |Rfun P.X (a:ℝ) (d:ℝ) - (rStar d : ℝ)| ≤ 14 * P.H / S.D := by
    intro d hin hdlo hdhi
    obtain ⟨-, hDd, hDda, -⟩ := hin
    have hdpos : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hDSpos hdlo
    have hd2 : (0:ℝ) < (d:ℝ) ^ 2 := by positivity
    have hda2 : (0:ℝ) < ((d:ℝ) + a) ^ 2 := by positivity
    obtain ⟨e1lo, e1hi⟩ := hgetm_spec d hd2 hDd
    have hDda' : inD P.X P.H (d + a) := hDda
    have hcast : ((d + a : ℤ):ℝ) = (d:ℝ) + (a:ℝ) := by push_cast; ring
    obtain ⟨e2lo, e2hi⟩ := hgetm_spec (d + a) (by rw [hcast]; positivity) hDda'
    rw [hcast] at e2lo e2hi
    have hrcast : (rStar d : ℝ)
        = -(2 * (d:ℝ) - a) * (getm d : ℝ) + (2 * (d:ℝ) + 3 * a) * (getm (d + a) : ℝ) := by
      rw [hrStar]; push_cast; ring
    exact Rfun_near_int P.X P.H (a:ℝ) (d:ℝ) S.D hXpos hHpos hDSpos haRpos
      (by rw [← hDeq]; exact haD) hdlo hdhi (getm d) (getm (d + a))
      e1lo e1hi e2lo e2hi (rStar d) hrcast
  -- R_a(d) ≍ R on [D,2D]
  have hRfun_bds : ∀ d : ℤ, S.D ≤ (d:ℝ) → (d:ℝ) ≤ 2 * S.D →
      S.R / 36 ≤ Rfun P.X (a:ℝ) (d:ℝ) ∧ Rfun P.X (a:ℝ) (d:ℝ) ≤ 8 * S.R := by
    intro d hdlo hdhi
    have hdpos : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hDSpos hdlo
    have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
    have hdane : (d:ℝ) + a ≠ 0 := by positivity
    have hfac : Rfun P.X (a:ℝ) (d:ℝ) = P.X * (a:ℝ) ^ 3 / ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) :=
      Rfun_factor P.X (a:ℝ) (d:ℝ) hdne hdane
    have haD' : (a:ℝ) ≤ S.D := by rw [← hDeq]; exact haD
    have hden : (0:ℝ) < (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 := by positivity
    have hd2ub : (d:ℝ) ^ 2 ≤ 4 * S.D ^ 2 := by nlinarith [hdlo, hdhi, hdpos.le]
    have hdaub : ((d:ℝ) + a) ^ 2 ≤ 9 * S.D ^ 2 := by nlinarith [hdhi, haD', haRpos.le, hdpos.le]
    have hd2lb : S.D ^ 2 ≤ (d:ℝ) ^ 2 := by nlinarith [hdlo, hdpos.le, hDSpos.le]
    have hdalb : S.D ^ 2 ≤ ((d:ℝ) + a) ^ 2 := by nlinarith [hdlo, haRpos.le, hdpos.le, hDSpos.le]
    have hprodub : (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 ≤ 36 * S.D ^ 4 := by
      calc (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 ≤ (4 * S.D ^ 2) * (9 * S.D ^ 2) :=
            mul_le_mul hd2ub hdaub (by positivity) (by positivity)
        _ = 36 * S.D ^ 4 := by ring
    have hprodlb : S.D ^ 4 ≤ (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 := by
      calc S.D ^ 4 = S.D ^ 2 * S.D ^ 2 := by ring
        _ ≤ (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 :=
            mul_le_mul hd2lb hdalb (by positivity) (by positivity)
    have hAcube : S.A ^ 3 ≤ (a:ℝ) ^ 3 := pow_le_pow_left₀ hApos.le hAa 3
    have hacube : (a:ℝ) ^ 3 ≤ 8 * S.A ^ 3 := by
      nlinarith [pow_le_pow_left₀ haRpos.le haA 3, hApos.le]
    have hD4pos : (0:ℝ) < S.D ^ 4 := by positivity
    have hSRprod : S.R * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) = P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) / S.D ^ 4 := by
      rw [hRval]; ring
    constructor
    · -- lower:  S.R/36 ≤ X a³/(d²(d+a)²)
      rw [hfac, div_le_div_iff₀ (by positivity) hden]
      -- need  S.R * (d²(d+a)²) ≤ X a³ * 36
      rw [hSRprod, div_le_iff₀ hD4pos]
      have hXA : P.X * S.A ^ 3 ≤ P.X * (a:ℝ) ^ 3 := mul_le_mul_of_nonneg_left hAcube hXpos.le
      calc P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2)
          ≤ P.X * (a:ℝ) ^ 3 * (36 * S.D ^ 4) :=
            mul_le_mul hXA hprodub (by positivity) (by positivity)
        _ = P.X * (a:ℝ) ^ 3 * 36 * S.D ^ 4 := by ring
    · -- upper:  X a³/(d²(d+a)²) ≤ 8 S.R
      rw [hfac, div_le_iff₀ hden, hRval]
      rw [show (8:ℝ) * (P.X * S.A ^ 3 / S.D ^ 4) * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2)
          = 8 * P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) / S.D ^ 4 by ring]
      rw [le_div_iff₀ hD4pos]
      have hXa : P.X * (a:ℝ) ^ 3 ≤ P.X * (8 * S.A ^ 3) := mul_le_mul_of_nonneg_left hacube hXpos.le
      calc P.X * (a:ℝ) ^ 3 * S.D ^ 4
          ≤ P.X * (8 * S.A ^ 3) * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) :=
            mul_le_mul hXa hprodlb (by positivity) (by positivity)
        _ = 8 * P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) := by ring
  -- the underlying set 𝒟_a ∩ [⌈D⌉, ⌊2D⌋]
  set S₀ : Finset ℤ := (Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter (fun d => inDa P.X P.H a d) with hS₀
  have hDaCard : DaCard P.X P.H a D = S₀.card := by rw [DaCard, hS₀]
  -- membership facts for d ∈ S₀
  have hmemS₀ : ∀ d ∈ S₀, inDa P.X P.H a d ∧ S.D ≤ (d:ℝ) ∧ (d:ℝ) ≤ 2 * S.D := by
    intro d hd
    rw [hS₀, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hlo, hhi⟩, hin⟩ := hd
    refine ⟨hin, ?_, ?_⟩
    · have : (⌈D⌉ : ℝ) ≤ (d:ℝ) := by exact_mod_cast hlo
      rw [← hDeq]; linarith [Int.le_ceil D, this]
    · have : (d:ℝ) ≤ (⌊2 * D⌋ : ℝ) := by exact_mod_cast hhi
      rw [← hDeq]; linarith [Int.floor_le (2 * D), this]
  -- rounding error 14/Δ ≤ R/72  (since R ≥ 32768 and 14 H/D = 14/Δ ≤ 14)
  have herr_small : 14 * P.H / S.D ≤ S.R / 72 := by
    have hHD : 14 * P.H / S.D = 14 / S.Δ := by rw [hDSeq]; field_simp
    rw [hHD]
    -- 14/Δ ≤ (32768/Δ)/72 ≤ R/72  (uses the degraded `hRlb : 32768/Δ ≤ R`)
    have h1 : (14:ℝ) / S.Δ ≤ (32768 / S.Δ) / 72 := by
      rw [div_div, div_le_div_iff₀ hΔpos (by positivity)]; nlinarith [hΔpos]
    have h2 : (32768 / S.Δ) / 72 ≤ S.R / 72 := by gcongr
    linarith
  -- for d ∈ S₀:  R_a(d) ∈ [R/36, 8R], and rStar d ∈ [R/72, 9R] as a real
  have hrStar_band : ∀ d ∈ S₀, S.R / 72 ≤ (rStar d : ℝ) ∧ (rStar d : ℝ) ≤ 16 * S.R := by
    intro d hd
    obtain ⟨hin, hdlo, hdhi⟩ := hmemS₀ d hd
    obtain ⟨hRlo, hRhi⟩ := hRfun_bds d hdlo hdhi
    have hn := hnear d hin hdlo hdhi
    rw [abs_le] at hn
    refine ⟨?_, ?_⟩
    · -- rStar d ≥ Rfun − 14/Δ ≥ R/36 − R/72 = R/72
      have : (rStar d : ℝ) ≥ Rfun P.X (a:ℝ) (d:ℝ) - 14 * P.H / S.D := by linarith [hn.1]
      linarith [hRlo, herr_small, this]
    · have : (rStar d : ℝ) ≤ Rfun P.X (a:ℝ) (d:ℝ) + 14 * P.H / S.D := by linarith [hn.2]
      linarith [hRhi, herr_small, this, hRpos]
  -- rStar d is a positive integer for d ∈ S₀
  have hrStar_pos : ∀ d ∈ S₀, 0 < rStar d := by
    intro d hd
    have := (hrStar_band d hd).1
    have hR72 : (0:ℝ) < S.R / 72 := by positivity
    have : (0:ℝ) < (rStar d : ℝ) := lt_of_lt_of_le hR72 this
    exact_mod_cast this
  -- the value map to ℕ, and Ra
  set rN : ℤ → ℕ := fun d => (rStar d).toNat with hrN
  set Ra : Finset ℕ := S₀.image rN with hRa
  -- for d ∈ S₀,  (rN d : ℝ) = (rStar d : ℝ)
  have hrNcast : ∀ d ∈ S₀, ((rN d : ℤ) : ℝ) = (rStar d : ℝ) := by
    intro d hd
    rw [hrN]; simp only [Int.toNat_of_nonneg (hrStar_pos d hd).le]
  -- dStar : choose a preimage in S₀
  set dStar : ℕ → ℤ := fun r =>
    if h : ∃ d ∈ S₀, rN d = r then h.choose else 0 with hdStar
  have hdStar_spec : ∀ r ∈ Ra, dStar r ∈ S₀ ∧ rN (dStar r) = r := by
    intro r hr
    rw [hRa, Finset.mem_image] at hr
    have hex : ∃ d ∈ S₀, rN d = r := by
      obtain ⟨d, hd, hdr⟩ := hr; exact ⟨d, hd, hdr⟩
    have hval : dStar r = hex.choose := by rw [hdStar]; simp only [hex, dif_pos]
    obtain ⟨hmem, heq⟩ := hex.choose_spec
    rw [hval]; exact ⟨hmem, heq⟩
  -- spacing threshold, spread budget, and the (Δ/A)^{8/3}G^{-2/3} budget
  set spc : ℝ := c * (a:ℝ) ^ (-1/3 : ℝ) * S.Δ ^ (5/3 : ℝ) * (P.H ^ 5 / P.X) ^ (1/3 : ℝ) with hspcdef
  set Wbud : ℝ := 9072 * S.D ^ 5 / (S.Δ * P.X * (a:ℝ) ^ 3) with hWdef
  set tgt : ℝ := (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ) with htgtdef
  have hspc_pos : 0 < spc := by
    obtain ⟨hp, -⟩ := spc_pos_cube P.X P.H S.Δ (a:ℝ) hXpos hHpos hΔpos haRpos
    rw [hspcdef]
    -- spc here uses lemma_3_1's c, not 1/10; positivity directly
    have h1 : (0:ℝ) < (a:ℝ) ^ (-1/3 : ℝ) := Real.rpow_pos_of_pos haRpos _
    have h2 : (0:ℝ) < S.Δ ^ (5/3 : ℝ) := Real.rpow_pos_of_pos hΔpos _
    have h3 : (0:ℝ) ≤ (P.H ^ 5 / P.X) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
    positivity
  have hW_pos : 0 < Wbud := by rw [hWdef]; positivity
  have htgt_pos : 0 < tgt := by
    obtain ⟨hp, -⟩ := target_pos_cube S.Δ S.A P.G hΔpos hApos hGpos
    rw [htgtdef]; exact hp
  -- spread budget bound:  Wbud ≤ S.D/2
  have hW_half : Wbud ≤ S.D / 2 := by
    rw [hWdef, div_le_iff₀ (by positivity)]
    -- 9072 D⁵ ≤ (S.D/2)(Δ X a³) = D Δ X a³/2
    have hD5 : S.D ^ 5 = S.D ^ 4 * S.D := by ring
    have hDeqv : S.D = P.H * S.Δ := hDSeq
    -- lowered threshold: X a³ ≥ 262144 Δ³ H⁴ ⇒ (HΔ²/2)·X·a³ ≥ 131072 H⁵ Δ⁵ ≥ 9072 H⁵ Δ⁵
    have hXa3 : (262144 : ℝ) * S.Δ ^ (3:ℕ) * P.H ^ 4 ≤ (a:ℝ) ^ 3 * P.X := by
      have e : (262144 : ℝ) * S.Δ ^ (3:ℕ) * (P.H ^ 4 / P.X) * P.X
          = 262144 * S.Δ ^ (3:ℕ) * P.H ^ 4 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right ha3 hXpos.le, e]
    have hD4 : S.D ^ 4 = S.Δ ^ (4:ℕ) * P.H ^ 4 := by rw [hDeqv]; ring
    rw [hD5, hD4, hDeqv]
    have hcoef : (0:ℝ) ≤ P.H * S.Δ ^ 2 / 2 := by positivity
    have hmul : (P.H * S.Δ ^ 2 / 2) * ((262144:ℝ) * S.Δ ^ (3:ℕ) * P.H ^ 4)
        ≤ (P.H * S.Δ ^ 2 / 2) * ((a:ℝ) ^ 3 * P.X) :=
      mul_le_mul_of_nonneg_left hXa3 hcoef
    nlinarith [hmul, hΔ, pow_pos hHpos 5, pow_pos hΔpos 5, mul_pos hHpos hΔpos,
      mul_nonneg (pow_pos hHpos 5).le (pow_pos hΔpos 5).le]
  -- the cube comparison:  2 Wbud / spc ≤ (18144/c) tgt
  have hWspc : 2 * Wbud / spc ≤ (18144 / c) * tgt := by
    obtain ⟨-, hspc3⟩ := spc_pos_cube P.X P.H S.Δ (a:ℝ) hXpos hHpos hΔpos haRpos
    obtain ⟨-, htgt3⟩ := target_pos_cube S.Δ S.A P.G hΔpos hApos hGpos
    -- spc³ with lemma_3_1's c:  spc³ = c³ Δ⁵(H⁵/X)/a
    have hspc3' : spc ^ 3 = c ^ 3 * S.Δ ^ (5:ℕ) * (P.H ^ 5 / P.X) / (a:ℝ) := by
      have e1 : ((a:ℝ) ^ (-1/3 : ℝ)) ^ (3:ℕ) = (a:ℝ)⁻¹ := by
        rw [← Real.rpow_natCast ((a:ℝ) ^ (-1/3 : ℝ)) 3, ← Real.rpow_mul haRpos.le]
        rw [show (-1/3 : ℝ) * (3:ℕ) = (-1 : ℝ) by push_cast; ring, Real.rpow_neg_one]
      have e2 : (S.Δ ^ (5/3 : ℝ)) ^ (3:ℕ) = S.Δ ^ (5 : ℕ) := by
        rw [← Real.rpow_natCast (S.Δ ^ (5/3 : ℝ)) 3, ← Real.rpow_mul hΔpos.le]
        rw [show (5/3 : ℝ) * (3:ℕ) = (5 : ℕ) by push_cast; ring, Real.rpow_natCast]
      have e3 : ((P.H ^ 5 / P.X) ^ (1/3 : ℝ)) ^ (3:ℕ) = P.H ^ 5 / P.X := by
        rw [← Real.rpow_natCast ((P.H ^ 5 / P.X) ^ (1/3 : ℝ)) 3,
          ← Real.rpow_mul (by positivity)]; norm_num
      rw [hspcdef]
      rw [show (c * (a:ℝ) ^ (-1/3 : ℝ) * S.Δ ^ (5/3 : ℝ) * (P.H ^ 5 / P.X) ^ (1/3 : ℝ)) ^ 3
          = c ^ 3 * ((a:ℝ) ^ (-1/3 : ℝ)) ^ (3:ℕ) * (S.Δ ^ (5/3 : ℝ)) ^ (3:ℕ)
            * ((P.H ^ 5 / P.X) ^ (1/3 : ℝ)) ^ (3:ℕ) by ring]
      rw [e1, e2, e3]; field_simp
    -- prove the multiplied form  2 Wbud ≤ (18144/c) tgt spc, then divide by spc
    have hmain : 2 * Wbud ≤ (18144 / c) * tgt * spc := by
      have hlhs_nn : (0:ℝ) ≤ 2 * Wbud := by positivity
      have hrhs_nn : (0:ℝ) ≤ (18144 / c) * tgt * spc := by positivity
      apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hrhs_nn
      -- cubes
      have hl3 : (2 * Wbud) ^ 3 = 8 * Wbud ^ 3 := by ring
      have hr3 : ((18144 / c) * tgt * spc) ^ 3
          = (5973090729984 / c ^ 3) * tgt ^ 3 * spc ^ 3 := by
        rw [mul_pow, mul_pow, show (18144 / c) ^ 3 = 5973090729984 / c ^ 3 by ring]
      rw [hl3, hr3, hspc3', htgt3, hWdef]
      have hX_GH : P.X = P.G * P.H ^ 5 := P.X_eq_G_mul_H_pow_five
      have hD_HΔ : S.D = P.H * S.Δ := hDSeq
      have hAcube8 : S.A ^ (8:ℕ) ≤ (a:ℝ) ^ (8:ℕ) := pow_le_pow_left₀ hApos.le hAa 8
      rw [hD_HΔ, hX_GH]
      -- both sides as single fractions
      have hLHS : 8 * (9072 * (P.H * S.Δ) ^ 5 / (S.Δ * (P.G * P.H ^ 5) * (a:ℝ) ^ 3)) ^ 3
          = (8 * 9072 ^ 3) * P.H ^ 15 * S.Δ ^ 15 / (S.Δ ^ 3 * P.G ^ 3 * P.H ^ 15 * (a:ℝ) ^ 9) := by
        rw [div_pow, mul_div_assoc']; congr 1 <;> ring
      have hRHS : 5973090729984 / c ^ 3 * (S.Δ ^ 8 / (S.A ^ 8 * P.G ^ 2))
            * (c ^ 3 * S.Δ ^ 5 * (P.H ^ 5 / (P.G * P.H ^ 5)) / (a:ℝ))
          = 5973090729984 * S.Δ ^ 13 / (S.A ^ 8 * P.G ^ 3 * (a:ℝ)) := by
        field_simp
      rw [hLHS, hRHS, div_le_div_iff₀ (by positivity) (by positivity)]
      -- reduces to  A⁸ ≤ Δ a⁸  times a positive monomial
      have hDa8 : S.A ^ (8:ℕ) ≤ S.Δ * (a:ℝ) ^ (8:ℕ) := by
        calc S.A ^ (8:ℕ) ≤ (a:ℝ) ^ (8:ℕ) := hAcube8
          _ ≤ S.Δ * (a:ℝ) ^ (8:ℕ) := by nlinarith [hΔ, pow_pos haRpos 8]
      have hfac : (0:ℝ) ≤ 5973090729984 * S.Δ ^ 15 * P.G ^ 3 * P.H ^ 15 * (a:ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hDa8 hfac]
    rw [div_le_iff₀ hspc_pos]; exact hmain
  refine ⟨Ra, dStar, ?_, ?_, ?_, ?_⟩
  · -- (1) dStar r ∈ 𝒟_a
    intro r hr
    obtain ⟨hmem, -⟩ := hdStar_spec r hr
    exact (hmemS₀ (dStar r) hmem).1
  · -- (2) r ≍ R band  (c₁ = 1/72, C₁ = 16)
    intro r hr
    obtain ⟨hmem, heq⟩ := hdStar_spec r hr
    obtain ⟨hlo, hhi⟩ := hrStar_band (dStar r) hmem
    have hcast : (r : ℝ) = (rStar (dStar r) : ℝ) := by
      have h := hrNcast (dStar r) hmem
      rw [heq] at h
      push_cast at h
      linarith [h]
    rw [hcast]
    exact ⟨by linarith [hlo], by linarith [hhi]⟩
  · -- (3) the fiber bound
    rw [hDaCard]
    -- rN maps S₀ into Ra
    have hmaps : (↑S₀ : Set ℤ).MapsTo rN ↑Ra := by
      intro d hd; rw [hRa]; exact Finset.mem_image_of_mem rN hd
    -- per-fiber bound
    set C₂ : ℝ := 18144 / c + 2 with hC₂def
    have hC₂pos : 0 < C₂ := by rw [hC₂def]; positivity
    have hfiber : ∀ r ∈ Ra, (((S₀.filter (fun d => rN d = r)).card : ℕ) : ℝ) ≤ C₂ * (1 + tgt) := by
      intro r hr
      set Fr : Finset ℤ := S₀.filter (fun d => rN d = r) with hFrdef
      have hFrsub : ∀ d ∈ Fr, d ∈ S₀ ∧ rN d = r := by
        intro d hd; rw [hFrdef, Finset.mem_filter] at hd; exact hd
      -- rStar d = r on Fr
      have hFr_rStar : ∀ d ∈ Fr, (rStar d : ℝ) = (r:ℝ) := by
        intro d hd
        obtain ⟨hdS₀, hdr⟩ := hFrsub d hd
        have := hrNcast d hdS₀; rw [hdr] at this; push_cast at this; linarith [this]
      -- |R_a(d) − r| ≤ 14 H/D on Fr
      have hRr : ∀ d ∈ Fr, |Rfun P.X (a:ℝ) (d:ℝ) - (r:ℝ)| ≤ 14 * P.H / S.D := by
        intro d hd
        obtain ⟨hdS₀, -⟩ := hFrsub d hd
        obtain ⟨hind, hdlo, hdhi⟩ := hmemS₀ d hdS₀
        have hnd := hnear d hind hdlo hdhi
        rw [← hFr_rStar d hd]; exact hnd
      -- spread bound (uses Rfun_diff_lb_abs)
      have hspread : ∀ d d'' : ℤ, d ∈ Fr → d'' ∈ Fr → (d'':ℝ) - (d:ℝ) ≤ Wbud := by
        intro d d'' hd hd''
        obtain ⟨hdS₀, -⟩ := hFrsub d hd
        obtain ⟨hd''S₀, -⟩ := hFrsub d'' hd''
        obtain ⟨-, hdlo, hdhi⟩ := hmemS₀ d hdS₀
        obtain ⟨-, hd''lo, hd''hi⟩ := hmemS₀ d'' hd''S₀
        have hRcd := hRr d hd
        have hRcd'' := hRr d'' hd''
        rw [abs_le] at hRcd hRcd''
        have h28 : (28:ℝ) * P.H / S.D = 14 * P.H / S.D + 14 * P.H / S.D := by ring
        have hRclose : |Rfun P.X (a:ℝ) (d:ℝ) - Rfun P.X (a:ℝ) (d'':ℝ)| ≤ 28 * P.H / S.D := by
          rw [abs_le]; rw [h28]
          constructor <;> linarith [hRcd.1, hRcd.2, hRcd''.1, hRcd''.2]
        have haDD : (a:ℝ) ≤ S.D := by rw [← hDeq]; exact haD
        have hlb := Rfun_diff_lb_abs P.X (a:ℝ) (d:ℝ) (d'':ℝ) S.D hXpos hDSpos haRpos
          haDD hdlo hdhi hd''lo hd''hi
        -- (1/324) X a³ |d−d''|/D⁵ ≤ 28 H/D  ⇒  |d−d''| ≤ Wbud
        have hcomb : (1/324 : ℝ) * P.X * (a:ℝ) ^ 3 * |(d:ℝ) - (d'':ℝ)| / S.D ^ 5 ≤ 28 * P.H / S.D :=
          le_trans hlb hRclose
        have hXa3pos : (0:ℝ) < P.X * (a:ℝ) ^ 3 := by positivity
        have hD5pos : (0:ℝ) < S.D ^ 5 := by positivity
        have hWval : Wbud = 9072 * P.H * S.D ^ 4 / (P.X * (a:ℝ) ^ 3) := by
          rw [hWdef]
          rw [show S.D ^ 5 = S.D ^ 4 * (P.H * S.Δ) by rw [hDSeq]; ring,
            show S.Δ * P.X * (a:ℝ) ^ 3 = (P.X * (a:ℝ) ^ 3) * S.Δ by ring]
          rw [mul_comm (S.D ^ 4) (P.H * S.Δ)]
          field_simp
        -- |d−d''| ≤ Wbud, hence d''−d ≤ |d−d''| ≤ Wbud
        have hdd_abs : |(d:ℝ) - (d'':ℝ)| ≤ Wbud := by
          rw [hWval, le_div_iff₀ hXa3pos]
          rw [div_le_iff₀ hD5pos] at hcomb
          have hHDS : 28 * P.H / S.D * S.D ^ 5 = 28 * P.H * S.D ^ 4 := by
            rw [hDSeq]; field_simp
          have hstep : (1/324 : ℝ) * P.X * (a:ℝ) ^ 3 * |(d:ℝ) - (d'':ℝ)| ≤ 28 * P.H * S.D ^ 4 := by
            rw [← hHDS]; exact hcomb
          nlinarith [hstep, abs_nonneg ((d:ℝ) - (d'':ℝ))]
        have : (d'':ℝ) - (d:ℝ) ≤ |(d:ℝ) - (d'':ℝ)| := by
          rw [abs_sub_comm]; exact le_abs_self _
        linarith [this, hdd_abs]
      -- gap bound (uses lemma_3_1)
      have hgap : ∀ d d'' : ℤ, d ∈ Fr → d'' ∈ Fr → d < d'' →
          (∃ d' ∈ Fr, d < d' ∧ d' < d'') → spc ≤ (d'':ℝ) - (d:ℝ) := by
        intro d d'' hd hd'' hlt hbtw
        obtain ⟨hdS₀, -⟩ := hFrsub d hd
        obtain ⟨hd''S₀, -⟩ := hFrsub d'' hd''
        obtain ⟨hind, hdlo, hdhi⟩ := hmemS₀ d hdS₀
        obtain ⟨hind'', -, -⟩ := hmemS₀ d'' hd''S₀
        obtain ⟨d', hd'Fr, hlt1, hlt2⟩ := hbtw
        obtain ⟨hd'S₀, -⟩ := hFrsub d' hd'Fr
        obtain ⟨hind', -, -⟩ := hmemS₀ d' hd'S₀
        set b : ℤ := d'' - d with hbdef
        have hbpos : 0 < b := by rw [hbdef]; omega
        have hdb : d + b = d'' := by rw [hbdef]; ring
        have hb_real : (b:ℝ) ≤ S.D / 2 := by
          have := hspread d d'' hd hd''
          have hbcast : (b:ℝ) = (d'':ℝ) - (d:ℝ) := by rw [hbdef]; push_cast; ring
          rw [hbcast]; linarith [this, hW_half]
        have hspacing := hc P S a ha d b hbpos hind (by rw [hdb]; exact hind'')
          ⟨d', hlt1, by rw [hdb]; exact hlt2, hind'⟩ ⟨hdlo, hdhi⟩ hb_real ha_lo hΔlo hX0
        have hbcast : (b:ℝ) = (d'':ℝ) - (d:ℝ) := by rw [hbdef]; push_cast; ring
        rw [hspcdef]; rw [← hbcast]; exact hspacing
      -- apply gap_card_bound
      have hgcb := gap_card_bound Fr spc Wbud hspc_pos hW_pos.le hgap hspread
      -- #Fr ≤ 2 + 2 Wbud/spc ≤ 2 + (18144/c) tgt ≤ C₂(1+tgt)
      have h2W : 2 + 2 * Wbud / spc ≤ C₂ * (1 + tgt) := by
        rw [hC₂def]
        have htnn : 0 ≤ tgt := htgt_pos.le
        nlinarith [hWspc, htnn, hc_pos, div_nonneg (by norm_num : (0:ℝ) ≤ 18144) hc_pos.le]
      calc (((S₀.filter (fun d => rN d = r)).card : ℕ) : ℝ)
          = ((Fr.card : ℕ) : ℝ) := by rw [hFrdef]
        _ ≤ 2 + 2 * Wbud / spc := hgcb
        _ ≤ C₂ * (1 + tgt) := h2W
    -- sum over Ra
    have hsum : S₀.card = ∑ r ∈ Ra, (S₀.filter (fun d => rN d = r)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    have : (S₀.card : ℝ) = ∑ r ∈ Ra, ((S₀.filter (fun d => rN d = r)).card : ℝ) := by
      rw [hsum]; push_cast; rfl
    rw [this]
    calc ∑ r ∈ Ra, ((S₀.filter (fun d => rN d = r)).card : ℝ)
        ≤ ∑ _r ∈ Ra, C₂ * (1 + tgt) := Finset.sum_le_sum hfiber
      _ = (Ra.card : ℝ) * (C₂ * (1 + tgt)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = C₂ * (Ra.card : ℝ) * (1 + tgt) := by ring
  · -- (4) approximation:  |dStar r − dtil r| ≤ 4536 (Δ/G)(Δ³/A³)
    intro r hr
    obtain ⟨hmem, heq⟩ := hdStar_spec r hr
    obtain ⟨hin, hdlo, hdhi⟩ := hmemS₀ (dStar r) hmem
    have hrcast : (r : ℝ) = (rStar (dStar r) : ℝ) := by
      have h := hrNcast (dStar r) hmem
      rw [heq] at h; push_cast at h; linarith [h]
    -- r in band
    obtain ⟨hblo, hbhi⟩ := hrStar_band (dStar r) hmem
    have hbandlo : (1/72 : ℝ) * S.R ≤ (r:ℝ) := by rw [hrcast]; linarith [hblo]
    have hbandhi : (r:ℝ) ≤ 16 * S.R := by rw [hrcast]; linarith [hbhi]
    obtain ⟨hdtilR, hdtillo, hdtilhi⟩ := hdtil (r:ℝ) hbandlo hbandhi
    -- |Rfun(dStar r) − Rfun(dtil r)| ≤ 14/Δ
    have hn := hnear (dStar r) hin hdlo hdhi
    rw [abs_le] at hn
    have hRdiff : |Rfun P.X (a:ℝ) ((dStar r):ℝ) - Rfun P.X (a:ℝ) (dtil (r:ℝ))| ≤ 14 * P.H / S.D := by
      rw [hdtilR, hrcast]
      rw [abs_le]; exact ⟨by linarith [hn.1], by linarith [hn.2]⟩
    -- algebraic MVT lower bound
    have haDD : (a:ℝ) ≤ S.D := by rw [← hDeq]; exact haD
    have hlb := Rfun_diff_lb_abs P.X (a:ℝ) ((dStar r):ℝ) (dtil (r:ℝ)) S.D hXpos hDSpos haRpos
      haDD hdlo hdhi hdtillo hdtilhi
    -- so (1/324) X a³ |Δd| / D⁵ ≤ 14/Δ ⇒ |Δd| ≤ 4536 D⁵/(Δ X a³)
    have hcomb : (1/324 : ℝ) * P.X * (a:ℝ) ^ 3 * |((dStar r):ℝ) - dtil (r:ℝ)| / S.D ^ 5 ≤ 14 * P.H / S.D :=
      le_trans hlb hRdiff
    have hXa3pos : (0:ℝ) < P.X * (a:ℝ) ^ 3 := by positivity
    have hD5pos : (0:ℝ) < S.D ^ 5 := by positivity
    -- |Δd| ≤ 324 · 14 · D⁵ · H / (X a³ · D)  = 4536 D⁴ H/(X a³)
    have habs : |((dStar r):ℝ) - dtil (r:ℝ)| ≤ 4536 * S.D ^ 4 * P.H / (P.X * (a:ℝ) ^ 3) := by
      rw [div_le_iff₀ hD5pos] at hcomb
      rw [le_div_iff₀ hXa3pos]
      have hDeq5 : S.D ^ 5 = S.D ^ 4 * S.D := by ring
      have hHDS : 14 * P.H / S.D * S.D ^ 5 = 14 * P.H * S.D ^ 4 := by
        rw [hDSeq]; field_simp
      have hstep : (1/324 : ℝ) * P.X * (a:ℝ) ^ 3 * |((dStar r):ℝ) - dtil (r:ℝ)| ≤ 14 * P.H * S.D ^ 4 := by
        rw [← hHDS]; exact hcomb
      nlinarith [hstep, abs_nonneg (((dStar r):ℝ) - dtil (r:ℝ))]
    -- finally bound by 4536 (Δ/G)(Δ³/A³)
    refine le_trans habs ?_
    -- 4536 D⁴ H/(X a³) ≤ 4536 (Δ/G)(Δ³/A³)  ⟺  D⁴ H A³/(X a³) ≤ Δ⁴/G  (uses A ≤ a, D=HΔ, X=GH⁵)
    rw [show (4536:ℝ) * (S.Δ / P.G) * (S.Δ ^ 3 / S.A ^ 3) = 4536 * S.Δ ^ 4 / (P.G * S.A ^ 3) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    -- 4536 D⁴ H * (G A³) ≤ 4536 Δ⁴ * (X a³)
    have hXGH : P.X = P.G * P.H ^ 5 := P.X_eq_G_mul_H_pow_five
    have hD4 : S.D ^ 4 = P.H ^ 4 * S.Δ ^ 4 := by rw [hDSeq]; ring
    have hAcube : S.A ^ 3 ≤ (a:ℝ) ^ 3 := pow_le_pow_left₀ hApos.le hAa 3
    rw [hD4, hXGH]
    -- goal: 4536 * (H⁴Δ⁴) * H * (G * A³) ≤ 4536 * Δ⁴ * ((G H⁵) * a³)
    have hGH5 : (0:ℝ) < P.G * P.H ^ 5 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hAcube (by positivity : (0:ℝ) ≤ 4536 * (P.H ^ 4 * S.Δ ^ 4) * P.H * P.G),
      hApos.le, hGpos.le, hHpos.le, hΔpos.le]

set_option maxHeartbeats 1600000 in
/-- **Prop 3.2 fiber bound only** (the `dtil`-free part of `prop_3_2`).

The fiber/spacing construction never uses the right-inverse `dtil`; this variant exposes just
the `ℛ_a` band and the (stated weak) fiber bound `#𝒟_a ≪ #ℛ_a·(1+(Δ/A)^{8/3}G^{-2/3})`, which
is all §8/§9 need.  Proof reuses the same `ℛ_a` construction as `prop_3_2`, dropping the two
clauses (`dStar r ∈ 𝒟_a`, approximation) which are the only ones touching `dtil`. -/
theorem prop_3_2_fiber : ∃ (c₁ C₁ C₂ : ℝ), 0 < c₁ ∧ 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ), 0 < a → P.X ^ (1/100 : ℝ) ≤ S.Δ →
      (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
      (1/4:ℝ) * S.Δ^(4/3:ℝ) * (P.H^4/P.X)^(1/3:ℝ) ≤ (a:ℝ) →
      S.A ≤ (a:ℝ) → (a:ℝ) ≤ 2*S.A → 2*S.A ≤ S.D →
      ∀ (D : ℝ), 0 < D → D = S.D →
        ∃ Ra : Finset ℕ, (∀ r ∈ Ra, c₁*S.R ≤ (r:ℝ) ∧ (r:ℝ) ≤ C₁*S.R) ∧
          ((DaCard P.X P.H a D : ℝ) ≤ C₂ * (Ra.card:ℝ) * (1 + (S.Δ/S.A)^(8/3:ℝ) * P.G^(-2/3:ℝ))) := by
  obtain ⟨c, hc_pos, hc⟩ := lemma_3_1
  refine ⟨1/72, 16, 18144 / c + 2, by norm_num, by norm_num, by positivity, ?_⟩
  intro P S a ha hΔlo hX0 ha_lo hAa haA hAD D hDpos hDeq
  have hΔ : (16777216 : ℝ) ≤ S.Δ := le_trans hX0 hΔlo
  have hXpos : 0 < P.X := P.X_pos
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDSeq : S.D = P.H * S.Δ := rfl
  have hDSpos : 0 < S.D := by rw [hDSeq]; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have haRpos : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have haD : (a:ℝ) ≤ D := by rw [hDeq]; linarith [haA, hAD]
  have hRval : S.R = P.X * S.A ^ 3 / S.D ^ 4 := by
    rw [S.R_eq_orig, hDSeq]; rw [show (P.H * S.Δ) ^ 4 = S.Δ ^ 4 * P.H ^ 4 by ring]
  have ha3 : (262144 : ℝ) * S.Δ ^ (3:ℕ) * (P.H ^ 4 / P.X) ≤ (a:ℝ) ^ 3 :=
    a_cubed_lb_quarter P.X P.H S.Δ a hXpos hΔpos haRpos (by linarith [hΔ]) ha_lo
  -- with the lowered threshold the band lower bound degrades to `R ≥ 32768/Δ`
  have hRlb : (32768 : ℝ) / S.Δ ≤ S.R := by
    have hAge : (a:ℝ) / 2 ≤ S.A := by linarith [haA]
    have hAcube : ((a:ℝ) / 2) ^ 3 ≤ S.A ^ 3 := pow_le_pow_left₀ (by positivity) hAge 3
    have hD4 : S.D ^ 4 = S.Δ ^ (4:ℕ) * P.H ^ 4 := by rw [hDSeq]; ring
    have hD4pos : (0:ℝ) < S.D ^ 4 := by positivity
    rw [hRval, div_le_div_iff₀ hΔpos hD4pos, hD4]
    have haX : (262144 : ℝ) * S.Δ ^ (3:ℕ) * P.H ^ 4 ≤ (a:ℝ) ^ 3 * P.X := by
      have e : (262144 : ℝ) * S.Δ ^ (3:ℕ) * (P.H ^ 4 / P.X) * P.X
          = 262144 * S.Δ ^ (3:ℕ) * P.H ^ 4 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right ha3 hXpos.le, e]
    have hPXA : P.X * ((a:ℝ)/2) ^ 3 ≤ P.X * S.A ^ 3 :=
      mul_le_mul_of_nonneg_left hAcube hXpos.le
    -- goal: 32768 * (S.Δ⁴ H⁴) ≤ (X A³) * S.Δ;  use X a³ ≥ 262144 Δ³ H⁴, A³ ≥ (a/2)³
    have hΔ4 : S.Δ ^ (4:ℕ) = S.Δ ^ (3:ℕ) * S.Δ := by ring
    rw [hΔ4]
    nlinarith [haX, hPXA, hXpos.le, mul_le_mul_of_nonneg_right haX hΔpos.le,
      mul_pos hΔpos (pow_pos hΔpos 3)]
  classical
  set getm : ℤ → ℤ := fun d =>
    if h : (∃ m : ℤ, P.X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ P.X + P.H)
      then h.choose else 0 with hgetm
  have hgetm_spec : ∀ d : ℤ, (0:ℝ) < (d:ℝ) ^ 2 → inD P.X P.H d →
      0 ≤ (getm d : ℝ) - P.X / (d:ℝ) ^ 2 ∧ (getm d : ℝ) - P.X / (d:ℝ) ^ 2 ≤ P.H / (d:ℝ) ^ 2 := by
    intro d hd2 hin
    have hex : (∃ m : ℤ, P.X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ P.X + P.H) := hin
    have hval : getm d = hex.choose := by rw [hgetm]; simp only [hex, dif_pos]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    rw [hval]
    have hne : (d:ℝ) ^ 2 ≠ 0 := ne_of_gt hd2
    have key : ((hex.choose:ℝ) - P.X / (d:ℝ) ^ 2) * (d:ℝ) ^ 2 = (hex.choose:ℝ) * (d:ℝ) ^ 2 - P.X := by
      rw [sub_mul, div_mul_cancel₀ P.X hne]
    constructor
    · have h0 : 0 ≤ ((hex.choose:ℝ) - P.X / (d:ℝ) ^ 2) * (d:ℝ) ^ 2 := by rw [key]; linarith
      exact (mul_nonneg_iff_of_pos_right hd2).mp h0
    · rw [le_div_iff₀ hd2, key]; linarith
  set rStar : ℤ → ℤ := fun d =>
    -(2 * d - a) * getm d + (2 * d + 3 * a) * getm (d + a) with hrStar
  have hnear : ∀ d : ℤ, inDa P.X P.H a d → S.D ≤ (d:ℝ) → (d:ℝ) ≤ 2 * S.D →
      |Rfun P.X (a:ℝ) (d:ℝ) - (rStar d : ℝ)| ≤ 14 * P.H / S.D := by
    intro d hin hdlo hdhi
    obtain ⟨-, hDd, hDda, -⟩ := hin
    have hdpos : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hDSpos hdlo
    have hd2 : (0:ℝ) < (d:ℝ) ^ 2 := by positivity
    have hda2 : (0:ℝ) < ((d:ℝ) + a) ^ 2 := by positivity
    obtain ⟨e1lo, e1hi⟩ := hgetm_spec d hd2 hDd
    have hDda' : inD P.X P.H (d + a) := hDda
    have hcast : ((d + a : ℤ):ℝ) = (d:ℝ) + (a:ℝ) := by push_cast; ring
    obtain ⟨e2lo, e2hi⟩ := hgetm_spec (d + a) (by rw [hcast]; positivity) hDda'
    rw [hcast] at e2lo e2hi
    have hrcast : (rStar d : ℝ)
        = -(2 * (d:ℝ) - a) * (getm d : ℝ) + (2 * (d:ℝ) + 3 * a) * (getm (d + a) : ℝ) := by
      rw [hrStar]; push_cast; ring
    exact Rfun_near_int P.X P.H (a:ℝ) (d:ℝ) S.D hXpos hHpos hDSpos haRpos
      (by rw [← hDeq]; exact haD) hdlo hdhi (getm d) (getm (d + a))
      e1lo e1hi e2lo e2hi (rStar d) hrcast
  have hRfun_bds : ∀ d : ℤ, S.D ≤ (d:ℝ) → (d:ℝ) ≤ 2 * S.D →
      S.R / 36 ≤ Rfun P.X (a:ℝ) (d:ℝ) ∧ Rfun P.X (a:ℝ) (d:ℝ) ≤ 8 * S.R := by
    intro d hdlo hdhi
    have hdpos : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hDSpos hdlo
    have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
    have hdane : (d:ℝ) + a ≠ 0 := by positivity
    have hfac : Rfun P.X (a:ℝ) (d:ℝ) = P.X * (a:ℝ) ^ 3 / ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) :=
      Rfun_factor P.X (a:ℝ) (d:ℝ) hdne hdane
    have haD' : (a:ℝ) ≤ S.D := by rw [← hDeq]; exact haD
    have hden : (0:ℝ) < (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 := by positivity
    have hd2ub : (d:ℝ) ^ 2 ≤ 4 * S.D ^ 2 := by nlinarith [hdlo, hdhi, hdpos.le]
    have hdaub : ((d:ℝ) + a) ^ 2 ≤ 9 * S.D ^ 2 := by nlinarith [hdhi, haD', haRpos.le, hdpos.le]
    have hd2lb : S.D ^ 2 ≤ (d:ℝ) ^ 2 := by nlinarith [hdlo, hdpos.le, hDSpos.le]
    have hdalb : S.D ^ 2 ≤ ((d:ℝ) + a) ^ 2 := by nlinarith [hdlo, haRpos.le, hdpos.le, hDSpos.le]
    have hprodub : (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 ≤ 36 * S.D ^ 4 := by
      calc (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 ≤ (4 * S.D ^ 2) * (9 * S.D ^ 2) :=
            mul_le_mul hd2ub hdaub (by positivity) (by positivity)
        _ = 36 * S.D ^ 4 := by ring
    have hprodlb : S.D ^ 4 ≤ (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 := by
      calc S.D ^ 4 = S.D ^ 2 * S.D ^ 2 := by ring
        _ ≤ (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 :=
            mul_le_mul hd2lb hdalb (by positivity) (by positivity)
    have hAcube : S.A ^ 3 ≤ (a:ℝ) ^ 3 := pow_le_pow_left₀ hApos.le hAa 3
    have hacube : (a:ℝ) ^ 3 ≤ 8 * S.A ^ 3 := by
      nlinarith [pow_le_pow_left₀ haRpos.le haA 3, hApos.le]
    have hD4pos : (0:ℝ) < S.D ^ 4 := by positivity
    constructor
    · rw [hfac, div_le_div_iff₀ (by positivity) hden]
      rw [show S.R * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) = P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) / S.D ^ 4 by rw [hRval]; ring, div_le_iff₀ hD4pos]
      have hXA : P.X * S.A ^ 3 ≤ P.X * (a:ℝ) ^ 3 := mul_le_mul_of_nonneg_left hAcube hXpos.le
      calc P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2)
          ≤ P.X * (a:ℝ) ^ 3 * (36 * S.D ^ 4) :=
            mul_le_mul hXA hprodub (by positivity) (by positivity)
        _ = P.X * (a:ℝ) ^ 3 * 36 * S.D ^ 4 := by ring
    · rw [hfac, div_le_iff₀ hden, hRval]
      rw [show (8:ℝ) * (P.X * S.A ^ 3 / S.D ^ 4) * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2)
          = 8 * P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) / S.D ^ 4 by ring]
      rw [le_div_iff₀ hD4pos]
      have hXa : P.X * (a:ℝ) ^ 3 ≤ P.X * (8 * S.A ^ 3) := mul_le_mul_of_nonneg_left hacube hXpos.le
      calc P.X * (a:ℝ) ^ 3 * S.D ^ 4
          ≤ P.X * (8 * S.A ^ 3) * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) :=
            mul_le_mul hXa hprodlb (by positivity) (by positivity)
        _ = 8 * P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) := by ring
  set S₀ : Finset ℤ := (Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter (fun d => inDa P.X P.H a d) with hS₀
  have hDaCard : DaCard P.X P.H a D = S₀.card := by rw [DaCard, hS₀]
  have hmemS₀ : ∀ d ∈ S₀, inDa P.X P.H a d ∧ S.D ≤ (d:ℝ) ∧ (d:ℝ) ≤ 2 * S.D := by
    intro d hd
    rw [hS₀, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hlo, hhi⟩, hin⟩ := hd
    refine ⟨hin, ?_, ?_⟩
    · have : (⌈D⌉ : ℝ) ≤ (d:ℝ) := by exact_mod_cast hlo
      rw [← hDeq]; linarith [Int.le_ceil D, this]
    · have : (d:ℝ) ≤ (⌊2 * D⌋ : ℝ) := by exact_mod_cast hhi
      rw [← hDeq]; linarith [Int.floor_le (2 * D), this]
  have herr_small : 14 * P.H / S.D ≤ S.R / 72 := by
    have hHD : 14 * P.H / S.D = 14 / S.Δ := by rw [hDSeq]; field_simp
    rw [hHD]
    -- 14/Δ ≤ (32768/Δ)/72 ≤ R/72  (uses the degraded `hRlb : 32768/Δ ≤ R`)
    have h1 : (14:ℝ) / S.Δ ≤ (32768 / S.Δ) / 72 := by
      rw [div_div, div_le_div_iff₀ hΔpos (by positivity)]; nlinarith [hΔpos]
    have h2 : (32768 / S.Δ) / 72 ≤ S.R / 72 := by gcongr
    linarith
  have hrStar_band : ∀ d ∈ S₀, S.R / 72 ≤ (rStar d : ℝ) ∧ (rStar d : ℝ) ≤ 16 * S.R := by
    intro d hd
    obtain ⟨hin, hdlo, hdhi⟩ := hmemS₀ d hd
    obtain ⟨hRlo, hRhi⟩ := hRfun_bds d hdlo hdhi
    have hn := hnear d hin hdlo hdhi
    rw [abs_le] at hn
    refine ⟨?_, ?_⟩
    · have : (rStar d : ℝ) ≥ Rfun P.X (a:ℝ) (d:ℝ) - 14 * P.H / S.D := by linarith [hn.1]
      linarith [hRlo, herr_small, this]
    · have : (rStar d : ℝ) ≤ Rfun P.X (a:ℝ) (d:ℝ) + 14 * P.H / S.D := by linarith [hn.2]
      linarith [hRhi, herr_small, this, hRpos]
  have hrStar_pos : ∀ d ∈ S₀, 0 < rStar d := by
    intro d hd
    have := (hrStar_band d hd).1
    have hR72 : (0:ℝ) < S.R / 72 := by positivity
    have : (0:ℝ) < (rStar d : ℝ) := lt_of_lt_of_le hR72 this
    exact_mod_cast this
  set rN : ℤ → ℕ := fun d => (rStar d).toNat with hrN
  set Ra : Finset ℕ := S₀.image rN with hRa
  have hrNcast : ∀ d ∈ S₀, ((rN d : ℤ) : ℝ) = (rStar d : ℝ) := by
    intro d hd
    rw [hrN]; simp only [Int.toNat_of_nonneg (hrStar_pos d hd).le]
  set spc : ℝ := c * (a:ℝ) ^ (-1/3 : ℝ) * S.Δ ^ (5/3 : ℝ) * (P.H ^ 5 / P.X) ^ (1/3 : ℝ) with hspcdef
  set Wbud : ℝ := 9072 * S.D ^ 5 / (S.Δ * P.X * (a:ℝ) ^ 3) with hWdef
  set tgt : ℝ := (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ) with htgtdef
  have hspc_pos : 0 < spc := by
    rw [hspcdef]
    have h1 : (0:ℝ) < (a:ℝ) ^ (-1/3 : ℝ) := Real.rpow_pos_of_pos haRpos _
    have h2 : (0:ℝ) < S.Δ ^ (5/3 : ℝ) := Real.rpow_pos_of_pos hΔpos _
    have h3 : (0:ℝ) ≤ (P.H ^ 5 / P.X) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
    positivity
  have hW_pos : 0 < Wbud := by rw [hWdef]; positivity
  have htgt_pos : 0 < tgt := by
    obtain ⟨hp, -⟩ := target_pos_cube S.Δ S.A P.G hΔpos hApos hGpos
    rw [htgtdef]; exact hp
  have hW_half : Wbud ≤ S.D / 2 := by
    rw [hWdef, div_le_iff₀ (by positivity)]
    have hD5 : S.D ^ 5 = S.D ^ 4 * S.D := by ring
    have hDeqv : S.D = P.H * S.Δ := hDSeq
    -- now with the `Δ³` form of `ha3`
    have hXa3 : (262144 : ℝ) * S.Δ ^ (3:ℕ) * P.H ^ 4 ≤ (a:ℝ) ^ 3 * P.X := by
      have e : (262144 : ℝ) * S.Δ ^ (3:ℕ) * (P.H ^ 4 / P.X) * P.X
          = 262144 * S.Δ ^ (3:ℕ) * P.H ^ 4 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right ha3 hXpos.le, e]
    have hD4 : S.D ^ 4 = S.Δ ^ (4:ℕ) * P.H ^ 4 := by rw [hDeqv]; ring
    rw [hD5, hD4, hDeqv]
    have hcoef : (0:ℝ) ≤ P.H * S.Δ ^ 2 / 2 := by positivity
    have hmul : (P.H * S.Δ ^ 2 / 2) * ((262144:ℝ) * S.Δ ^ (3:ℕ) * P.H ^ 4)
        ≤ (P.H * S.Δ ^ 2 / 2) * ((a:ℝ) ^ 3 * P.X) :=
      mul_le_mul_of_nonneg_left hXa3 hcoef
    -- LHS goal 9072 H⁵Δ⁵ ≤ (HΔ²/2)·X·a³ ≥ (HΔ²/2)·262144 Δ³ H⁴ = 131072 H⁵ Δ⁵
    nlinarith [hmul, hΔ, pow_pos hHpos 5, pow_pos hΔpos 5, mul_pos hHpos hΔpos,
      mul_nonneg (pow_pos hHpos 5).le (pow_pos hΔpos 5).le]
  have hWspc : 2 * Wbud / spc ≤ (18144 / c) * tgt := by
    obtain ⟨-, hspc3⟩ := spc_pos_cube P.X P.H S.Δ (a:ℝ) hXpos hHpos hΔpos haRpos
    obtain ⟨-, htgt3⟩ := target_pos_cube S.Δ S.A P.G hΔpos hApos hGpos
    have hspc3' : spc ^ 3 = c ^ 3 * S.Δ ^ (5:ℕ) * (P.H ^ 5 / P.X) / (a:ℝ) := by
      have e1 : ((a:ℝ) ^ (-1/3 : ℝ)) ^ (3:ℕ) = (a:ℝ)⁻¹ := by
        rw [← Real.rpow_natCast ((a:ℝ) ^ (-1/3 : ℝ)) 3, ← Real.rpow_mul haRpos.le]
        rw [show (-1/3 : ℝ) * (3:ℕ) = (-1 : ℝ) by push_cast; ring, Real.rpow_neg_one]
      have e2 : (S.Δ ^ (5/3 : ℝ)) ^ (3:ℕ) = S.Δ ^ (5 : ℕ) := by
        rw [← Real.rpow_natCast (S.Δ ^ (5/3 : ℝ)) 3, ← Real.rpow_mul hΔpos.le]
        rw [show (5/3 : ℝ) * (3:ℕ) = (5 : ℕ) by push_cast; ring, Real.rpow_natCast]
      have e3 : ((P.H ^ 5 / P.X) ^ (1/3 : ℝ)) ^ (3:ℕ) = P.H ^ 5 / P.X := by
        rw [← Real.rpow_natCast ((P.H ^ 5 / P.X) ^ (1/3 : ℝ)) 3,
          ← Real.rpow_mul (by positivity)]; norm_num
      rw [hspcdef]
      rw [show (c * (a:ℝ) ^ (-1/3 : ℝ) * S.Δ ^ (5/3 : ℝ) * (P.H ^ 5 / P.X) ^ (1/3 : ℝ)) ^ 3
          = c ^ 3 * ((a:ℝ) ^ (-1/3 : ℝ)) ^ (3:ℕ) * (S.Δ ^ (5/3 : ℝ)) ^ (3:ℕ)
            * ((P.H ^ 5 / P.X) ^ (1/3 : ℝ)) ^ (3:ℕ) by ring]
      rw [e1, e2, e3]; field_simp
    have hmain : 2 * Wbud ≤ (18144 / c) * tgt * spc := by
      have hrhs_nn : (0:ℝ) ≤ (18144 / c) * tgt * spc := by positivity
      apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hrhs_nn
      have hl3 : (2 * Wbud) ^ 3 = 8 * Wbud ^ 3 := by ring
      have hr3 : ((18144 / c) * tgt * spc) ^ 3
          = (5973090729984 / c ^ 3) * tgt ^ 3 * spc ^ 3 := by
        rw [mul_pow, mul_pow, show (18144 / c) ^ 3 = 5973090729984 / c ^ 3 by ring]
      rw [hl3, hr3, hspc3', htgt3, hWdef]
      have hX_GH : P.X = P.G * P.H ^ 5 := P.X_eq_G_mul_H_pow_five
      have hD_HΔ : S.D = P.H * S.Δ := hDSeq
      have hAcube8 : S.A ^ (8:ℕ) ≤ (a:ℝ) ^ (8:ℕ) := pow_le_pow_left₀ hApos.le hAa 8
      rw [hD_HΔ, hX_GH]
      have hLHS : 8 * (9072 * (P.H * S.Δ) ^ 5 / (S.Δ * (P.G * P.H ^ 5) * (a:ℝ) ^ 3)) ^ 3
          = (8 * 9072 ^ 3) * P.H ^ 15 * S.Δ ^ 15 / (S.Δ ^ 3 * P.G ^ 3 * P.H ^ 15 * (a:ℝ) ^ 9) := by
        rw [div_pow, mul_div_assoc']; congr 1 <;> ring
      have hRHS : 5973090729984 / c ^ 3 * (S.Δ ^ 8 / (S.A ^ 8 * P.G ^ 2))
            * (c ^ 3 * S.Δ ^ 5 * (P.H ^ 5 / (P.G * P.H ^ 5)) / (a:ℝ))
          = 5973090729984 * S.Δ ^ 13 / (S.A ^ 8 * P.G ^ 3 * (a:ℝ)) := by
        field_simp
      rw [hLHS, hRHS, div_le_div_iff₀ (by positivity) (by positivity)]
      have hDa8 : S.A ^ (8:ℕ) ≤ S.Δ * (a:ℝ) ^ (8:ℕ) := by
        calc S.A ^ (8:ℕ) ≤ (a:ℝ) ^ (8:ℕ) := hAcube8
          _ ≤ S.Δ * (a:ℝ) ^ (8:ℕ) := by nlinarith [hΔ, pow_pos haRpos 8]
      have hfac : (0:ℝ) ≤ 5973090729984 * S.Δ ^ 15 * P.G ^ 3 * P.H ^ 15 * (a:ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hDa8 hfac]
    rw [div_le_iff₀ hspc_pos]; exact hmain
  refine ⟨Ra, ?_, ?_⟩
  · -- band  (c₁ = 1/72, C₁ = 16)
    intro r hr
    rw [hRa, Finset.mem_image] at hr
    obtain ⟨d, hd, hdr⟩ := hr
    obtain ⟨hlo, hhi⟩ := hrStar_band d hd
    have hcast : (r : ℝ) = (rStar d : ℝ) := by
      have h := hrNcast d hd; rw [hdr] at h; push_cast at h; linarith [h]
    rw [hcast]
    exact ⟨by linarith [hlo], by linarith [hhi]⟩
  · -- the fiber bound
    rw [hDaCard]
    have hmaps : (↑S₀ : Set ℤ).MapsTo rN ↑Ra := by
      intro d hd; rw [hRa]; exact Finset.mem_image_of_mem rN hd
    set C₂ : ℝ := 18144 / c + 2 with hC₂def
    have hfiber : ∀ r ∈ Ra, (((S₀.filter (fun d => rN d = r)).card : ℕ) : ℝ) ≤ C₂ * (1 + tgt) := by
      intro r hr
      set Fr : Finset ℤ := S₀.filter (fun d => rN d = r) with hFrdef
      have hFrsub : ∀ d ∈ Fr, d ∈ S₀ ∧ rN d = r := by
        intro d hd; rw [hFrdef, Finset.mem_filter] at hd; exact hd
      have hFr_rStar : ∀ d ∈ Fr, (rStar d : ℝ) = (r:ℝ) := by
        intro d hd
        obtain ⟨hdS₀, hdr⟩ := hFrsub d hd
        have := hrNcast d hdS₀; rw [hdr] at this; push_cast at this; linarith [this]
      have hRr : ∀ d ∈ Fr, |Rfun P.X (a:ℝ) (d:ℝ) - (r:ℝ)| ≤ 14 * P.H / S.D := by
        intro d hd
        obtain ⟨hdS₀, -⟩ := hFrsub d hd
        obtain ⟨hind, hdlo, hdhi⟩ := hmemS₀ d hdS₀
        have hnd := hnear d hind hdlo hdhi
        rw [← hFr_rStar d hd]; exact hnd
      have hspread : ∀ d d'' : ℤ, d ∈ Fr → d'' ∈ Fr → (d'':ℝ) - (d:ℝ) ≤ Wbud := by
        intro d d'' hd hd''
        obtain ⟨hdS₀, -⟩ := hFrsub d hd
        obtain ⟨hd''S₀, -⟩ := hFrsub d'' hd''
        obtain ⟨-, hdlo, hdhi⟩ := hmemS₀ d hdS₀
        obtain ⟨-, hd''lo, hd''hi⟩ := hmemS₀ d'' hd''S₀
        have hRcd := hRr d hd
        have hRcd'' := hRr d'' hd''
        rw [abs_le] at hRcd hRcd''
        have h28 : (28:ℝ) * P.H / S.D = 14 * P.H / S.D + 14 * P.H / S.D := by ring
        have hRclose : |Rfun P.X (a:ℝ) (d:ℝ) - Rfun P.X (a:ℝ) (d'':ℝ)| ≤ 28 * P.H / S.D := by
          rw [abs_le]; rw [h28]
          constructor <;> linarith [hRcd.1, hRcd.2, hRcd''.1, hRcd''.2]
        have haDD : (a:ℝ) ≤ S.D := by rw [← hDeq]; exact haD
        have hlb := Rfun_diff_lb_abs P.X (a:ℝ) (d:ℝ) (d'':ℝ) S.D hXpos hDSpos haRpos
          haDD hdlo hdhi hd''lo hd''hi
        have hcomb : (1/324 : ℝ) * P.X * (a:ℝ) ^ 3 * |(d:ℝ) - (d'':ℝ)| / S.D ^ 5 ≤ 28 * P.H / S.D :=
          le_trans hlb hRclose
        have hXa3pos : (0:ℝ) < P.X * (a:ℝ) ^ 3 := by positivity
        have hD5pos : (0:ℝ) < S.D ^ 5 := by positivity
        have hWval : Wbud = 9072 * P.H * S.D ^ 4 / (P.X * (a:ℝ) ^ 3) := by
          rw [hWdef]
          rw [show S.D ^ 5 = S.D ^ 4 * (P.H * S.Δ) by rw [hDSeq]; ring,
            show S.Δ * P.X * (a:ℝ) ^ 3 = (P.X * (a:ℝ) ^ 3) * S.Δ by ring]
          rw [mul_comm (S.D ^ 4) (P.H * S.Δ)]; field_simp
        have hdd_abs : |(d:ℝ) - (d'':ℝ)| ≤ Wbud := by
          rw [hWval, le_div_iff₀ hXa3pos]
          rw [div_le_iff₀ hD5pos] at hcomb
          have hHDS : 28 * P.H / S.D * S.D ^ 5 = 28 * P.H * S.D ^ 4 := by rw [hDSeq]; field_simp
          have hstep : (1/324 : ℝ) * P.X * (a:ℝ) ^ 3 * |(d:ℝ) - (d'':ℝ)| ≤ 28 * P.H * S.D ^ 4 := by
            rw [← hHDS]; exact hcomb
          nlinarith [hstep, abs_nonneg ((d:ℝ) - (d'':ℝ))]
        have : (d'':ℝ) - (d:ℝ) ≤ |(d:ℝ) - (d'':ℝ)| := by rw [abs_sub_comm]; exact le_abs_self _
        linarith [this, hdd_abs]
      have hgap : ∀ d d'' : ℤ, d ∈ Fr → d'' ∈ Fr → d < d'' →
          (∃ d' ∈ Fr, d < d' ∧ d' < d'') → spc ≤ (d'':ℝ) - (d:ℝ) := by
        intro d d'' hd hd'' hlt hbtw
        obtain ⟨hdS₀, -⟩ := hFrsub d hd
        obtain ⟨hd''S₀, -⟩ := hFrsub d'' hd''
        obtain ⟨hind, hdlo, hdhi⟩ := hmemS₀ d hdS₀
        obtain ⟨hind'', -, -⟩ := hmemS₀ d'' hd''S₀
        obtain ⟨d', hd'Fr, hlt1, hlt2⟩ := hbtw
        obtain ⟨hd'S₀, -⟩ := hFrsub d' hd'Fr
        obtain ⟨hind', -, -⟩ := hmemS₀ d' hd'S₀
        set b : ℤ := d'' - d with hbdef
        have hbpos : 0 < b := by rw [hbdef]; omega
        have hdb : d + b = d'' := by rw [hbdef]; ring
        have hb_real : (b:ℝ) ≤ S.D / 2 := by
          have := hspread d d'' hd hd''
          have hbcast : (b:ℝ) = (d'':ℝ) - (d:ℝ) := by rw [hbdef]; push_cast; ring
          rw [hbcast]; linarith [this, hW_half]
        have hspacing := hc P S a ha d b hbpos hind (by rw [hdb]; exact hind'')
          ⟨d', hlt1, by rw [hdb]; exact hlt2, hind'⟩ ⟨hdlo, hdhi⟩ hb_real ha_lo hΔlo hX0
        have hbcast : (b:ℝ) = (d'':ℝ) - (d:ℝ) := by rw [hbdef]; push_cast; ring
        rw [hspcdef]; rw [← hbcast]; exact hspacing
      have hgcb := gap_card_bound Fr spc Wbud hspc_pos hW_pos.le hgap hspread
      have h2W : 2 + 2 * Wbud / spc ≤ C₂ * (1 + tgt) := by
        rw [hC₂def]
        have htnn : 0 ≤ tgt := htgt_pos.le
        nlinarith [hWspc, htnn, hc_pos, div_nonneg (by norm_num : (0:ℝ) ≤ 18144) hc_pos.le]
      calc (((S₀.filter (fun d => rN d = r)).card : ℕ) : ℝ)
          = ((Fr.card : ℕ) : ℝ) := by rw [hFrdef]
        _ ≤ 2 + 2 * Wbud / spc := hgcb
        _ ≤ C₂ * (1 + tgt) := h2W
    have hsum : S₀.card = ∑ r ∈ Ra, (S₀.filter (fun d => rN d = r)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    have : (S₀.card : ℝ) = ∑ r ∈ Ra, ((S₀.filter (fun d => rN d = r)).card : ℝ) := by
      rw [hsum]; push_cast; rfl
    rw [this]
    calc ∑ r ∈ Ra, ((S₀.filter (fun d => rN d = r)).card : ℝ)
        ≤ ∑ _r ∈ Ra, C₂ * (1 + tgt) := Finset.sum_le_sum hfiber
      _ = (Ra.card : ℝ) * (C₂ * (1 + tgt)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = C₂ * (Ra.card : ℝ) * (1 + tgt) := by ring

set_option maxHeartbeats 1600000 in
/-- **Prop 3.2 fiber bound + `dStar` localization** (the `dtil`-free part of `prop_3_2`, but also
returning the `dStar : ℕ → ℤ` with `dStar r ∈ 𝒟_a`).  Same construction as `prop_3_2_fiber`, but
additionally exposes the localization map `dStar`, which §7's `prop_7_3` needs (and which is built
in `prop_3_2`'s proof independently of the `dtil` right-inverse — only the approximation conjunct
touches `dtil`, and that is dropped here). -/
theorem prop_3_2_fiber_dStar : ∃ (c₁ C₁ C₂ : ℝ), 0 < c₁ ∧ 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (P : Globals) (S : Scale P) (a : ℤ), 0 < a → P.X ^ (1/100 : ℝ) ≤ S.Δ →
      (16777216 : ℝ) ≤ P.X ^ (1/100 : ℝ) →
      (1/4:ℝ) * S.Δ^(4/3:ℝ) * (P.H^4/P.X)^(1/3:ℝ) ≤ (a:ℝ) →
      S.A ≤ (a:ℝ) → (a:ℝ) ≤ 2*S.A → 2*S.A ≤ S.D →
      ∀ (D : ℝ), 0 < D → D = S.D →
        ∃ (Ra : Finset ℕ) (dStar : ℕ → ℤ),
          (∀ r ∈ Ra, inDa P.X P.H a (dStar r)) ∧
          (∀ r ∈ Ra, c₁*S.R ≤ (r:ℝ) ∧ (r:ℝ) ≤ C₁*S.R) ∧
          ((DaCard P.X P.H a D : ℝ) ≤ C₂ * (Ra.card:ℝ) * (1 + (S.Δ/S.A)^(8/3:ℝ) * P.G^(-2/3:ℝ))) := by
  obtain ⟨c, hc_pos, hc⟩ := lemma_3_1
  refine ⟨1/72, 16, 18144 / c + 2, by norm_num, by norm_num, by positivity, ?_⟩
  intro P S a ha hΔlo hX0 ha_lo hAa haA hAD D hDpos hDeq
  have hΔ : (16777216 : ℝ) ≤ S.Δ := le_trans hX0 hΔlo
  have hXpos : 0 < P.X := P.X_pos
  have hHpos : 0 < P.H := P.H_pos
  have hGpos : 0 < P.G := P.G_pos
  have hΔpos : 0 < S.Δ := S.Δ_pos
  have hΩpos : 0 < S.Ω := S.Ω_pos
  have hApos : 0 < S.A := by unfold Scale.A; positivity
  have hDSeq : S.D = P.H * S.Δ := rfl
  have hDSpos : 0 < S.D := by rw [hDSeq]; positivity
  have hRpos : 0 < S.R := by unfold Scale.R; positivity
  have haRpos : (0:ℝ) < (a:ℝ) := by exact_mod_cast ha
  have haD : (a:ℝ) ≤ D := by rw [hDeq]; linarith [haA, hAD]
  have hRval : S.R = P.X * S.A ^ 3 / S.D ^ 4 := by
    rw [S.R_eq_orig, hDSeq]; rw [show (P.H * S.Δ) ^ 4 = S.Δ ^ 4 * P.H ^ 4 by ring]
  have ha3 : (262144 : ℝ) * S.Δ ^ (3:ℕ) * (P.H ^ 4 / P.X) ≤ (a:ℝ) ^ 3 :=
    a_cubed_lb_quarter P.X P.H S.Δ a hXpos hΔpos haRpos (by linarith [hΔ]) ha_lo
  -- with the lowered threshold the band lower bound degrades to `R ≥ 32768/Δ`
  have hRlb : (32768 : ℝ) / S.Δ ≤ S.R := by
    have hAge : (a:ℝ) / 2 ≤ S.A := by linarith [haA]
    have hAcube : ((a:ℝ) / 2) ^ 3 ≤ S.A ^ 3 := pow_le_pow_left₀ (by positivity) hAge 3
    have hD4 : S.D ^ 4 = S.Δ ^ (4:ℕ) * P.H ^ 4 := by rw [hDSeq]; ring
    have hD4pos : (0:ℝ) < S.D ^ 4 := by positivity
    rw [hRval, div_le_div_iff₀ hΔpos hD4pos, hD4]
    have haX : (262144 : ℝ) * S.Δ ^ (3:ℕ) * P.H ^ 4 ≤ (a:ℝ) ^ 3 * P.X := by
      have e : (262144 : ℝ) * S.Δ ^ (3:ℕ) * (P.H ^ 4 / P.X) * P.X
          = 262144 * S.Δ ^ (3:ℕ) * P.H ^ 4 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right ha3 hXpos.le, e]
    have hPXA : P.X * ((a:ℝ)/2) ^ 3 ≤ P.X * S.A ^ 3 :=
      mul_le_mul_of_nonneg_left hAcube hXpos.le
    -- goal: 32768 * (S.Δ⁴ H⁴) ≤ (X A³) * S.Δ;  use X a³ ≥ 262144 Δ³ H⁴, A³ ≥ (a/2)³
    have hΔ4 : S.Δ ^ (4:ℕ) = S.Δ ^ (3:ℕ) * S.Δ := by ring
    rw [hΔ4]
    nlinarith [haX, hPXA, hXpos.le, mul_le_mul_of_nonneg_right haX hΔpos.le,
      mul_pos hΔpos (pow_pos hΔpos 3)]
  classical
  set getm : ℤ → ℤ := fun d =>
    if h : (∃ m : ℤ, P.X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ P.X + P.H)
      then h.choose else 0 with hgetm
  have hgetm_spec : ∀ d : ℤ, (0:ℝ) < (d:ℝ) ^ 2 → inD P.X P.H d →
      0 ≤ (getm d : ℝ) - P.X / (d:ℝ) ^ 2 ∧ (getm d : ℝ) - P.X / (d:ℝ) ^ 2 ≤ P.H / (d:ℝ) ^ 2 := by
    intro d hd2 hin
    have hex : (∃ m : ℤ, P.X ≤ (m : ℝ) * (d : ℝ) ^ 2 ∧ (m : ℝ) * (d : ℝ) ^ 2 ≤ P.X + P.H) := hin
    have hval : getm d = hex.choose := by rw [hgetm]; simp only [hex, dif_pos]
    obtain ⟨h1, h2⟩ := hex.choose_spec
    rw [hval]
    have hne : (d:ℝ) ^ 2 ≠ 0 := ne_of_gt hd2
    have key : ((hex.choose:ℝ) - P.X / (d:ℝ) ^ 2) * (d:ℝ) ^ 2 = (hex.choose:ℝ) * (d:ℝ) ^ 2 - P.X := by
      rw [sub_mul, div_mul_cancel₀ P.X hne]
    constructor
    · have h0 : 0 ≤ ((hex.choose:ℝ) - P.X / (d:ℝ) ^ 2) * (d:ℝ) ^ 2 := by rw [key]; linarith
      exact (mul_nonneg_iff_of_pos_right hd2).mp h0
    · rw [le_div_iff₀ hd2, key]; linarith
  set rStar : ℤ → ℤ := fun d =>
    -(2 * d - a) * getm d + (2 * d + 3 * a) * getm (d + a) with hrStar
  have hnear : ∀ d : ℤ, inDa P.X P.H a d → S.D ≤ (d:ℝ) → (d:ℝ) ≤ 2 * S.D →
      |Rfun P.X (a:ℝ) (d:ℝ) - (rStar d : ℝ)| ≤ 14 * P.H / S.D := by
    intro d hin hdlo hdhi
    obtain ⟨-, hDd, hDda, -⟩ := hin
    have hdpos : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hDSpos hdlo
    have hd2 : (0:ℝ) < (d:ℝ) ^ 2 := by positivity
    have hda2 : (0:ℝ) < ((d:ℝ) + a) ^ 2 := by positivity
    obtain ⟨e1lo, e1hi⟩ := hgetm_spec d hd2 hDd
    have hDda' : inD P.X P.H (d + a) := hDda
    have hcast : ((d + a : ℤ):ℝ) = (d:ℝ) + (a:ℝ) := by push_cast; ring
    obtain ⟨e2lo, e2hi⟩ := hgetm_spec (d + a) (by rw [hcast]; positivity) hDda'
    rw [hcast] at e2lo e2hi
    have hrcast : (rStar d : ℝ)
        = -(2 * (d:ℝ) - a) * (getm d : ℝ) + (2 * (d:ℝ) + 3 * a) * (getm (d + a) : ℝ) := by
      rw [hrStar]; push_cast; ring
    exact Rfun_near_int P.X P.H (a:ℝ) (d:ℝ) S.D hXpos hHpos hDSpos haRpos
      (by rw [← hDeq]; exact haD) hdlo hdhi (getm d) (getm (d + a))
      e1lo e1hi e2lo e2hi (rStar d) hrcast
  have hRfun_bds : ∀ d : ℤ, S.D ≤ (d:ℝ) → (d:ℝ) ≤ 2 * S.D →
      S.R / 36 ≤ Rfun P.X (a:ℝ) (d:ℝ) ∧ Rfun P.X (a:ℝ) (d:ℝ) ≤ 8 * S.R := by
    intro d hdlo hdhi
    have hdpos : (0:ℝ) < (d:ℝ) := lt_of_lt_of_le hDSpos hdlo
    have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdpos
    have hdane : (d:ℝ) + a ≠ 0 := by positivity
    have hfac : Rfun P.X (a:ℝ) (d:ℝ) = P.X * (a:ℝ) ^ 3 / ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) :=
      Rfun_factor P.X (a:ℝ) (d:ℝ) hdne hdane
    have haD' : (a:ℝ) ≤ S.D := by rw [← hDeq]; exact haD
    have hden : (0:ℝ) < (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 := by positivity
    have hd2ub : (d:ℝ) ^ 2 ≤ 4 * S.D ^ 2 := by nlinarith [hdlo, hdhi, hdpos.le]
    have hdaub : ((d:ℝ) + a) ^ 2 ≤ 9 * S.D ^ 2 := by nlinarith [hdhi, haD', haRpos.le, hdpos.le]
    have hd2lb : S.D ^ 2 ≤ (d:ℝ) ^ 2 := by nlinarith [hdlo, hdpos.le, hDSpos.le]
    have hdalb : S.D ^ 2 ≤ ((d:ℝ) + a) ^ 2 := by nlinarith [hdlo, haRpos.le, hdpos.le, hDSpos.le]
    have hprodub : (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 ≤ 36 * S.D ^ 4 := by
      calc (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 ≤ (4 * S.D ^ 2) * (9 * S.D ^ 2) :=
            mul_le_mul hd2ub hdaub (by positivity) (by positivity)
        _ = 36 * S.D ^ 4 := by ring
    have hprodlb : S.D ^ 4 ≤ (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 := by
      calc S.D ^ 4 = S.D ^ 2 * S.D ^ 2 := by ring
        _ ≤ (d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2 :=
            mul_le_mul hd2lb hdalb (by positivity) (by positivity)
    have hAcube : S.A ^ 3 ≤ (a:ℝ) ^ 3 := pow_le_pow_left₀ hApos.le hAa 3
    have hacube : (a:ℝ) ^ 3 ≤ 8 * S.A ^ 3 := by
      nlinarith [pow_le_pow_left₀ haRpos.le haA 3, hApos.le]
    have hD4pos : (0:ℝ) < S.D ^ 4 := by positivity
    constructor
    · rw [hfac, div_le_div_iff₀ (by positivity) hden]
      rw [show S.R * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) = P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) / S.D ^ 4 by rw [hRval]; ring, div_le_iff₀ hD4pos]
      have hXA : P.X * S.A ^ 3 ≤ P.X * (a:ℝ) ^ 3 := mul_le_mul_of_nonneg_left hAcube hXpos.le
      calc P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2)
          ≤ P.X * (a:ℝ) ^ 3 * (36 * S.D ^ 4) :=
            mul_le_mul hXA hprodub (by positivity) (by positivity)
        _ = P.X * (a:ℝ) ^ 3 * 36 * S.D ^ 4 := by ring
    · rw [hfac, div_le_iff₀ hden, hRval]
      rw [show (8:ℝ) * (P.X * S.A ^ 3 / S.D ^ 4) * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2)
          = 8 * P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) / S.D ^ 4 by ring]
      rw [le_div_iff₀ hD4pos]
      have hXa : P.X * (a:ℝ) ^ 3 ≤ P.X * (8 * S.A ^ 3) := mul_le_mul_of_nonneg_left hacube hXpos.le
      calc P.X * (a:ℝ) ^ 3 * S.D ^ 4
          ≤ P.X * (8 * S.A ^ 3) * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) :=
            mul_le_mul hXa hprodlb (by positivity) (by positivity)
        _ = 8 * P.X * S.A ^ 3 * ((d:ℝ) ^ 2 * ((d:ℝ) + a) ^ 2) := by ring
  set S₀ : Finset ℤ := (Finset.Icc ⌈D⌉ ⌊2 * D⌋).filter (fun d => inDa P.X P.H a d) with hS₀
  have hDaCard : DaCard P.X P.H a D = S₀.card := by rw [DaCard, hS₀]
  have hmemS₀ : ∀ d ∈ S₀, inDa P.X P.H a d ∧ S.D ≤ (d:ℝ) ∧ (d:ℝ) ≤ 2 * S.D := by
    intro d hd
    rw [hS₀, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hlo, hhi⟩, hin⟩ := hd
    refine ⟨hin, ?_, ?_⟩
    · have : (⌈D⌉ : ℝ) ≤ (d:ℝ) := by exact_mod_cast hlo
      rw [← hDeq]; linarith [Int.le_ceil D, this]
    · have : (d:ℝ) ≤ (⌊2 * D⌋ : ℝ) := by exact_mod_cast hhi
      rw [← hDeq]; linarith [Int.floor_le (2 * D), this]
  have herr_small : 14 * P.H / S.D ≤ S.R / 72 := by
    have hHD : 14 * P.H / S.D = 14 / S.Δ := by rw [hDSeq]; field_simp
    rw [hHD]
    -- 14/Δ ≤ (32768/Δ)/72 ≤ R/72  (uses the degraded `hRlb : 32768/Δ ≤ R`)
    have h1 : (14:ℝ) / S.Δ ≤ (32768 / S.Δ) / 72 := by
      rw [div_div, div_le_div_iff₀ hΔpos (by positivity)]; nlinarith [hΔpos]
    have h2 : (32768 / S.Δ) / 72 ≤ S.R / 72 := by gcongr
    linarith
  have hrStar_band : ∀ d ∈ S₀, S.R / 72 ≤ (rStar d : ℝ) ∧ (rStar d : ℝ) ≤ 16 * S.R := by
    intro d hd
    obtain ⟨hin, hdlo, hdhi⟩ := hmemS₀ d hd
    obtain ⟨hRlo, hRhi⟩ := hRfun_bds d hdlo hdhi
    have hn := hnear d hin hdlo hdhi
    rw [abs_le] at hn
    refine ⟨?_, ?_⟩
    · have : (rStar d : ℝ) ≥ Rfun P.X (a:ℝ) (d:ℝ) - 14 * P.H / S.D := by linarith [hn.1]
      linarith [hRlo, herr_small, this]
    · have : (rStar d : ℝ) ≤ Rfun P.X (a:ℝ) (d:ℝ) + 14 * P.H / S.D := by linarith [hn.2]
      linarith [hRhi, herr_small, this, hRpos]
  have hrStar_pos : ∀ d ∈ S₀, 0 < rStar d := by
    intro d hd
    have := (hrStar_band d hd).1
    have hR72 : (0:ℝ) < S.R / 72 := by positivity
    have : (0:ℝ) < (rStar d : ℝ) := lt_of_lt_of_le hR72 this
    exact_mod_cast this
  set rN : ℤ → ℕ := fun d => (rStar d).toNat with hrN
  set Ra : Finset ℕ := S₀.image rN with hRa
  have hrNcast : ∀ d ∈ S₀, ((rN d : ℤ) : ℝ) = (rStar d : ℝ) := by
    intro d hd
    rw [hrN]; simp only [Int.toNat_of_nonneg (hrStar_pos d hd).le]
  set dStar : ℕ → ℤ := fun r =>
    if h : ∃ d ∈ S₀, rN d = r then h.choose else 0 with hdStar
  have hdStar_spec : ∀ r ∈ Ra, dStar r ∈ S₀ ∧ rN (dStar r) = r := by
    intro r hr
    rw [hRa, Finset.mem_image] at hr
    have hex : ∃ d ∈ S₀, rN d = r := by
      obtain ⟨d, hd, hdr⟩ := hr; exact ⟨d, hd, hdr⟩
    have hval : dStar r = hex.choose := by rw [hdStar]; simp only [hex, dif_pos]
    obtain ⟨hmem, heq⟩ := hex.choose_spec
    rw [hval]; exact ⟨hmem, heq⟩
  set spc : ℝ := c * (a:ℝ) ^ (-1/3 : ℝ) * S.Δ ^ (5/3 : ℝ) * (P.H ^ 5 / P.X) ^ (1/3 : ℝ) with hspcdef
  set Wbud : ℝ := 9072 * S.D ^ 5 / (S.Δ * P.X * (a:ℝ) ^ 3) with hWdef
  set tgt : ℝ := (S.Δ / S.A) ^ (8/3 : ℝ) * P.G ^ (-2/3 : ℝ) with htgtdef
  have hspc_pos : 0 < spc := by
    rw [hspcdef]
    have h1 : (0:ℝ) < (a:ℝ) ^ (-1/3 : ℝ) := Real.rpow_pos_of_pos haRpos _
    have h2 : (0:ℝ) < S.Δ ^ (5/3 : ℝ) := Real.rpow_pos_of_pos hΔpos _
    have h3 : (0:ℝ) ≤ (P.H ^ 5 / P.X) ^ (1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
    positivity
  have hW_pos : 0 < Wbud := by rw [hWdef]; positivity
  have htgt_pos : 0 < tgt := by
    obtain ⟨hp, -⟩ := target_pos_cube S.Δ S.A P.G hΔpos hApos hGpos
    rw [htgtdef]; exact hp
  have hW_half : Wbud ≤ S.D / 2 := by
    rw [hWdef, div_le_iff₀ (by positivity)]
    have hD5 : S.D ^ 5 = S.D ^ 4 * S.D := by ring
    have hDeqv : S.D = P.H * S.Δ := hDSeq
    -- now with the `Δ³` form of `ha3`
    have hXa3 : (262144 : ℝ) * S.Δ ^ (3:ℕ) * P.H ^ 4 ≤ (a:ℝ) ^ 3 * P.X := by
      have e : (262144 : ℝ) * S.Δ ^ (3:ℕ) * (P.H ^ 4 / P.X) * P.X
          = 262144 * S.Δ ^ (3:ℕ) * P.H ^ 4 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right ha3 hXpos.le, e]
    have hD4 : S.D ^ 4 = S.Δ ^ (4:ℕ) * P.H ^ 4 := by rw [hDeqv]; ring
    rw [hD5, hD4, hDeqv]
    have hcoef : (0:ℝ) ≤ P.H * S.Δ ^ 2 / 2 := by positivity
    have hmul : (P.H * S.Δ ^ 2 / 2) * ((262144:ℝ) * S.Δ ^ (3:ℕ) * P.H ^ 4)
        ≤ (P.H * S.Δ ^ 2 / 2) * ((a:ℝ) ^ 3 * P.X) :=
      mul_le_mul_of_nonneg_left hXa3 hcoef
    -- LHS goal 9072 H⁵Δ⁵ ≤ (HΔ²/2)·X·a³ ≥ (HΔ²/2)·262144 Δ³ H⁴ = 131072 H⁵ Δ⁵
    nlinarith [hmul, hΔ, pow_pos hHpos 5, pow_pos hΔpos 5, mul_pos hHpos hΔpos,
      mul_nonneg (pow_pos hHpos 5).le (pow_pos hΔpos 5).le]
  have hWspc : 2 * Wbud / spc ≤ (18144 / c) * tgt := by
    obtain ⟨-, hspc3⟩ := spc_pos_cube P.X P.H S.Δ (a:ℝ) hXpos hHpos hΔpos haRpos
    obtain ⟨-, htgt3⟩ := target_pos_cube S.Δ S.A P.G hΔpos hApos hGpos
    have hspc3' : spc ^ 3 = c ^ 3 * S.Δ ^ (5:ℕ) * (P.H ^ 5 / P.X) / (a:ℝ) := by
      have e1 : ((a:ℝ) ^ (-1/3 : ℝ)) ^ (3:ℕ) = (a:ℝ)⁻¹ := by
        rw [← Real.rpow_natCast ((a:ℝ) ^ (-1/3 : ℝ)) 3, ← Real.rpow_mul haRpos.le]
        rw [show (-1/3 : ℝ) * (3:ℕ) = (-1 : ℝ) by push_cast; ring, Real.rpow_neg_one]
      have e2 : (S.Δ ^ (5/3 : ℝ)) ^ (3:ℕ) = S.Δ ^ (5 : ℕ) := by
        rw [← Real.rpow_natCast (S.Δ ^ (5/3 : ℝ)) 3, ← Real.rpow_mul hΔpos.le]
        rw [show (5/3 : ℝ) * (3:ℕ) = (5 : ℕ) by push_cast; ring, Real.rpow_natCast]
      have e3 : ((P.H ^ 5 / P.X) ^ (1/3 : ℝ)) ^ (3:ℕ) = P.H ^ 5 / P.X := by
        rw [← Real.rpow_natCast ((P.H ^ 5 / P.X) ^ (1/3 : ℝ)) 3,
          ← Real.rpow_mul (by positivity)]; norm_num
      rw [hspcdef]
      rw [show (c * (a:ℝ) ^ (-1/3 : ℝ) * S.Δ ^ (5/3 : ℝ) * (P.H ^ 5 / P.X) ^ (1/3 : ℝ)) ^ 3
          = c ^ 3 * ((a:ℝ) ^ (-1/3 : ℝ)) ^ (3:ℕ) * (S.Δ ^ (5/3 : ℝ)) ^ (3:ℕ)
            * ((P.H ^ 5 / P.X) ^ (1/3 : ℝ)) ^ (3:ℕ) by ring]
      rw [e1, e2, e3]; field_simp
    have hmain : 2 * Wbud ≤ (18144 / c) * tgt * spc := by
      have hrhs_nn : (0:ℝ) ≤ (18144 / c) * tgt * spc := by positivity
      apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hrhs_nn
      have hl3 : (2 * Wbud) ^ 3 = 8 * Wbud ^ 3 := by ring
      have hr3 : ((18144 / c) * tgt * spc) ^ 3
          = (5973090729984 / c ^ 3) * tgt ^ 3 * spc ^ 3 := by
        rw [mul_pow, mul_pow, show (18144 / c) ^ 3 = 5973090729984 / c ^ 3 by ring]
      rw [hl3, hr3, hspc3', htgt3, hWdef]
      have hX_GH : P.X = P.G * P.H ^ 5 := P.X_eq_G_mul_H_pow_five
      have hD_HΔ : S.D = P.H * S.Δ := hDSeq
      have hAcube8 : S.A ^ (8:ℕ) ≤ (a:ℝ) ^ (8:ℕ) := pow_le_pow_left₀ hApos.le hAa 8
      rw [hD_HΔ, hX_GH]
      have hLHS : 8 * (9072 * (P.H * S.Δ) ^ 5 / (S.Δ * (P.G * P.H ^ 5) * (a:ℝ) ^ 3)) ^ 3
          = (8 * 9072 ^ 3) * P.H ^ 15 * S.Δ ^ 15 / (S.Δ ^ 3 * P.G ^ 3 * P.H ^ 15 * (a:ℝ) ^ 9) := by
        rw [div_pow, mul_div_assoc']; congr 1 <;> ring
      have hRHS : 5973090729984 / c ^ 3 * (S.Δ ^ 8 / (S.A ^ 8 * P.G ^ 2))
            * (c ^ 3 * S.Δ ^ 5 * (P.H ^ 5 / (P.G * P.H ^ 5)) / (a:ℝ))
          = 5973090729984 * S.Δ ^ 13 / (S.A ^ 8 * P.G ^ 3 * (a:ℝ)) := by
        field_simp
      rw [hLHS, hRHS, div_le_div_iff₀ (by positivity) (by positivity)]
      have hDa8 : S.A ^ (8:ℕ) ≤ S.Δ * (a:ℝ) ^ (8:ℕ) := by
        calc S.A ^ (8:ℕ) ≤ (a:ℝ) ^ (8:ℕ) := hAcube8
          _ ≤ S.Δ * (a:ℝ) ^ (8:ℕ) := by nlinarith [hΔ, pow_pos haRpos 8]
      have hfac : (0:ℝ) ≤ 5973090729984 * S.Δ ^ 15 * P.G ^ 3 * P.H ^ 15 * (a:ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hDa8 hfac]
    rw [div_le_iff₀ hspc_pos]; exact hmain
  refine ⟨Ra, dStar, ?_, ?_, ?_⟩
  · -- (1) dStar r ∈ 𝒟_a
    intro r hr
    obtain ⟨hmem, -⟩ := hdStar_spec r hr
    exact (hmemS₀ (dStar r) hmem).1
  · -- (2) band  (c₁ = 1/72, C₁ = 16)
    intro r hr
    obtain ⟨hmem, heq⟩ := hdStar_spec r hr
    obtain ⟨hlo, hhi⟩ := hrStar_band (dStar r) hmem
    have hcast : (r : ℝ) = (rStar (dStar r) : ℝ) := by
      have h := hrNcast (dStar r) hmem; rw [heq] at h; push_cast at h; linarith [h]
    rw [hcast]
    exact ⟨by linarith [hlo], by linarith [hhi]⟩
  · -- (3) the fiber bound
    rw [hDaCard]
    have hmaps : (↑S₀ : Set ℤ).MapsTo rN ↑Ra := by
      intro d hd; rw [hRa]; exact Finset.mem_image_of_mem rN hd
    set C₂ : ℝ := 18144 / c + 2 with hC₂def
    have hfiber : ∀ r ∈ Ra, (((S₀.filter (fun d => rN d = r)).card : ℕ) : ℝ) ≤ C₂ * (1 + tgt) := by
      intro r hr
      set Fr : Finset ℤ := S₀.filter (fun d => rN d = r) with hFrdef
      have hFrsub : ∀ d ∈ Fr, d ∈ S₀ ∧ rN d = r := by
        intro d hd; rw [hFrdef, Finset.mem_filter] at hd; exact hd
      have hFr_rStar : ∀ d ∈ Fr, (rStar d : ℝ) = (r:ℝ) := by
        intro d hd
        obtain ⟨hdS₀, hdr⟩ := hFrsub d hd
        have := hrNcast d hdS₀; rw [hdr] at this; push_cast at this; linarith [this]
      have hRr : ∀ d ∈ Fr, |Rfun P.X (a:ℝ) (d:ℝ) - (r:ℝ)| ≤ 14 * P.H / S.D := by
        intro d hd
        obtain ⟨hdS₀, -⟩ := hFrsub d hd
        obtain ⟨hind, hdlo, hdhi⟩ := hmemS₀ d hdS₀
        have hnd := hnear d hind hdlo hdhi
        rw [← hFr_rStar d hd]; exact hnd
      have hspread : ∀ d d'' : ℤ, d ∈ Fr → d'' ∈ Fr → (d'':ℝ) - (d:ℝ) ≤ Wbud := by
        intro d d'' hd hd''
        obtain ⟨hdS₀, -⟩ := hFrsub d hd
        obtain ⟨hd''S₀, -⟩ := hFrsub d'' hd''
        obtain ⟨-, hdlo, hdhi⟩ := hmemS₀ d hdS₀
        obtain ⟨-, hd''lo, hd''hi⟩ := hmemS₀ d'' hd''S₀
        have hRcd := hRr d hd
        have hRcd'' := hRr d'' hd''
        rw [abs_le] at hRcd hRcd''
        have h28 : (28:ℝ) * P.H / S.D = 14 * P.H / S.D + 14 * P.H / S.D := by ring
        have hRclose : |Rfun P.X (a:ℝ) (d:ℝ) - Rfun P.X (a:ℝ) (d'':ℝ)| ≤ 28 * P.H / S.D := by
          rw [abs_le]; rw [h28]
          constructor <;> linarith [hRcd.1, hRcd.2, hRcd''.1, hRcd''.2]
        have haDD : (a:ℝ) ≤ S.D := by rw [← hDeq]; exact haD
        have hlb := Rfun_diff_lb_abs P.X (a:ℝ) (d:ℝ) (d'':ℝ) S.D hXpos hDSpos haRpos
          haDD hdlo hdhi hd''lo hd''hi
        have hcomb : (1/324 : ℝ) * P.X * (a:ℝ) ^ 3 * |(d:ℝ) - (d'':ℝ)| / S.D ^ 5 ≤ 28 * P.H / S.D :=
          le_trans hlb hRclose
        have hXa3pos : (0:ℝ) < P.X * (a:ℝ) ^ 3 := by positivity
        have hD5pos : (0:ℝ) < S.D ^ 5 := by positivity
        have hWval : Wbud = 9072 * P.H * S.D ^ 4 / (P.X * (a:ℝ) ^ 3) := by
          rw [hWdef]
          rw [show S.D ^ 5 = S.D ^ 4 * (P.H * S.Δ) by rw [hDSeq]; ring,
            show S.Δ * P.X * (a:ℝ) ^ 3 = (P.X * (a:ℝ) ^ 3) * S.Δ by ring]
          rw [mul_comm (S.D ^ 4) (P.H * S.Δ)]; field_simp
        have hdd_abs : |(d:ℝ) - (d'':ℝ)| ≤ Wbud := by
          rw [hWval, le_div_iff₀ hXa3pos]
          rw [div_le_iff₀ hD5pos] at hcomb
          have hHDS : 28 * P.H / S.D * S.D ^ 5 = 28 * P.H * S.D ^ 4 := by rw [hDSeq]; field_simp
          have hstep : (1/324 : ℝ) * P.X * (a:ℝ) ^ 3 * |(d:ℝ) - (d'':ℝ)| ≤ 28 * P.H * S.D ^ 4 := by
            rw [← hHDS]; exact hcomb
          nlinarith [hstep, abs_nonneg ((d:ℝ) - (d'':ℝ))]
        have : (d'':ℝ) - (d:ℝ) ≤ |(d:ℝ) - (d'':ℝ)| := by rw [abs_sub_comm]; exact le_abs_self _
        linarith [this, hdd_abs]
      have hgap : ∀ d d'' : ℤ, d ∈ Fr → d'' ∈ Fr → d < d'' →
          (∃ d' ∈ Fr, d < d' ∧ d' < d'') → spc ≤ (d'':ℝ) - (d:ℝ) := by
        intro d d'' hd hd'' hlt hbtw
        obtain ⟨hdS₀, -⟩ := hFrsub d hd
        obtain ⟨hd''S₀, -⟩ := hFrsub d'' hd''
        obtain ⟨hind, hdlo, hdhi⟩ := hmemS₀ d hdS₀
        obtain ⟨hind'', -, -⟩ := hmemS₀ d'' hd''S₀
        obtain ⟨d', hd'Fr, hlt1, hlt2⟩ := hbtw
        obtain ⟨hd'S₀, -⟩ := hFrsub d' hd'Fr
        obtain ⟨hind', -, -⟩ := hmemS₀ d' hd'S₀
        set b : ℤ := d'' - d with hbdef
        have hbpos : 0 < b := by rw [hbdef]; omega
        have hdb : d + b = d'' := by rw [hbdef]; ring
        have hb_real : (b:ℝ) ≤ S.D / 2 := by
          have := hspread d d'' hd hd''
          have hbcast : (b:ℝ) = (d'':ℝ) - (d:ℝ) := by rw [hbdef]; push_cast; ring
          rw [hbcast]; linarith [this, hW_half]
        have hspacing := hc P S a ha d b hbpos hind (by rw [hdb]; exact hind'')
          ⟨d', hlt1, by rw [hdb]; exact hlt2, hind'⟩ ⟨hdlo, hdhi⟩ hb_real ha_lo hΔlo hX0
        have hbcast : (b:ℝ) = (d'':ℝ) - (d:ℝ) := by rw [hbdef]; push_cast; ring
        rw [hspcdef]; rw [← hbcast]; exact hspacing
      have hgcb := gap_card_bound Fr spc Wbud hspc_pos hW_pos.le hgap hspread
      have h2W : 2 + 2 * Wbud / spc ≤ C₂ * (1 + tgt) := by
        rw [hC₂def]
        have htnn : 0 ≤ tgt := htgt_pos.le
        nlinarith [hWspc, htnn, hc_pos, div_nonneg (by norm_num : (0:ℝ) ≤ 18144) hc_pos.le]
      calc (((S₀.filter (fun d => rN d = r)).card : ℕ) : ℝ)
          = ((Fr.card : ℕ) : ℝ) := by rw [hFrdef]
        _ ≤ 2 + 2 * Wbud / spc := hgcb
        _ ≤ C₂ * (1 + tgt) := h2W
    have hsum : S₀.card = ∑ r ∈ Ra, (S₀.filter (fun d => rN d = r)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    have : (S₀.card : ℝ) = ∑ r ∈ Ra, ((S₀.filter (fun d => rN d = r)).card : ℝ) := by
      rw [hsum]; push_cast; rfl
    rw [this]
    calc ∑ r ∈ Ra, ((S₀.filter (fun d => rN d = r)).card : ℝ)
        ≤ ∑ _r ∈ Ra, C₂ * (1 + tgt) := Finset.sum_le_sum hfiber
      _ = (Ra.card : ℝ) * (C₂ * (1 + tgt)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = C₂ * (Ra.card : ℝ) * (1 + tgt) := by ring

end Squarefree
