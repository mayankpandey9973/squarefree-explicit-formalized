import Squarefree.Structure.ADecompAux
import Squarefree.Main
import Squarefree.ShortDeltaAux

/-!
# §3 A-decomposition (Nair–Roth) — self-contained, no §4

`#𝒟[D,2D] ≪ Σ_{threshold ≪ a ≪ ΔU} #𝒟_a`, with `threshold ≍ D^{4/3}/X^{1/3}`.

Proof (entirely self-contained; no Prop 4.3 / §4):
* **Gap pigeonhole.** Each `d ∈ 𝒟[D,2D]` (except the largest) has a unique 𝒟-successor at a
  gap `a`, hence lies in `𝒟_a`.
* **Tiny gaps are impossible** (`tiny_gap_impossible`): every gap is `≳ D³/X`.
* **Isolation** (`no_two_small_gaps`): among three consecutive 𝒟-elements two gaps cannot both
  be `≤ T₀ := (D⁴/(8X))^{1/3}/2`, so sub-threshold elements are an independent set in the path.
* **Large gaps.** `a ≫ ΔU` ⟹ those `d` are `≪ H/U`-spaced.

The combinatorial layer here injects the "Small" (sub-threshold) elements into their 𝒟-successors
(which are non-Small by isolation), counts the "Mid" (`T₀ < a ≤ ΔU`) block by the stated sum, and
the "Big" (`a > ΔU`) block by separation.
-/

open Classical Finset

namespace Squarefree

set_option maxHeartbeats 1000000

/-- Separated integers in `[lo, hi]` are few: if every two distinct elements of `T ⊆ Icc lo hi`
differ by `> g > 0`, then `#T ≤ (hi-lo)/g + 1`. -/
private theorem sep_card_bound (T : Finset ℤ) (lo hi : ℤ) (g : ℝ) (hg : 0 < g)
    (hlohi : (lo : ℝ) ≤ hi)
    (hsub : ∀ d ∈ T, lo ≤ d ∧ d ≤ hi)
    (hsep : ∀ d ∈ T, ∀ d' ∈ T, d < d' → g < (d' : ℝ) - d) :
    (T.card : ℝ) ≤ ((hi : ℝ) - lo) / g + 1 := by
  rcases T.eq_empty_or_nonempty with hempty | hne
  · subst hempty; simp only [Finset.card_empty, Nat.cast_zero]
    have : (0:ℝ) ≤ ((hi : ℝ) - lo) / g := by apply div_nonneg (by linarith) hg.le
    linarith
  set m := T.card with hm_def
  have hm0 : 0 < m := Finset.card_pos.mpr hne
  -- sorted enumeration
  set e := T.orderEmbOfFin (rfl : T.card = m) with he_def
  have hclamp : ∀ i : ℕ, min i (m - 1) < m := fun i => by omega
  set a : ℕ → ℤ := fun i => e ⟨min i (m - 1), hclamp i⟩ with ha_def
  have ha_mem : ∀ i, a i ∈ T := fun i => by rw [ha_def]; exact T.orderEmbOfFin_mem rfl _
  have ha_strict : ∀ i, i < m - 1 → a i < a (i + 1) := by
    intro i hi; rw [ha_def]; apply e.strictMono; simp only [Fin.mk_lt_mk]; omega
  -- gaps each `> g`
  set gp : ℕ → ℝ := fun i => (a (i + 1) : ℝ) - a i with hgp_def
  have hgp : ∀ i, i < m - 1 → g < gp i := by
    intro i hi
    have hlt := ha_strict i hi
    exact hsep (a i) (ha_mem i) (a (i + 1)) (ha_mem (i + 1)) hlt
  -- telescoping span
  have htel : ∑ i ∈ range (m - 1), gp i = (a (m - 1) : ℝ) - a 0 := by
    simp only [hgp_def]
    have := Finset.sum_range_sub (fun i => (a i : ℝ)) (m - 1)
    simpa using this
  have hspan_le : (a (m - 1) : ℝ) - a 0 ≤ (hi : ℝ) - lo := by
    have h1 := (hsub _ (ha_mem (m - 1))).2
    have h2 := (hsub _ (ha_mem 0)).1
    have : (a (m - 1) : ℝ) ≤ hi := by exact_mod_cast h1
    have : (lo : ℝ) ≤ a 0 := by exact_mod_cast h2
    push_cast at *; linarith
  -- span ≥ (m-1)·g
  have hspan_ge : ((m : ℝ) - 1) * g ≤ (a (m - 1) : ℝ) - a 0 := by
    rw [← htel]
    have hconst : ∑ _i ∈ range (m - 1), g = ((m : ℝ) - 1) * g := by
      rw [Finset.sum_const, card_range, nsmul_eq_mul]
      have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        have : 1 ≤ m := hm0; push_cast [Nat.cast_sub this]; ring
      rw [this]
    rw [← hconst]
    apply Finset.sum_le_sum
    intro i hi; exact le_of_lt (hgp i (mem_range.mp hi))
  -- combine: (m-1) ≤ (hi-lo)/g
  have hmle : ((m : ℝ) - 1) ≤ ((hi : ℝ) - lo) / g := by
    rw [le_div_iff₀ hg]; linarith [hspan_ge, hspan_le]
  linarith [hmle]

/-- Threshold cube identity: `(D^{4/3}/(2 X^{1/3}))³ = D⁴/(8X)`. -/
private theorem thr_cube (X D : ℝ) (hX : 0 < X) (hD : 0 < D) :
    (D ^ (4/3 : ℝ) / (2 * X ^ (1/3 : ℝ))) ^ 3 = D ^ 4 / (8 * X) := by
  have e1 : (D ^ (4/3 : ℝ)) ^ (3:ℕ) = D ^ (4:ℕ) := by
    rw [← Real.rpow_natCast (D ^ (4/3 : ℝ)) 3, ← Real.rpow_mul hD.le]
    rw [show (4/3 : ℝ) * (3:ℕ) = (4:ℕ) by push_cast; ring, Real.rpow_natCast]
  have e2 : (X ^ (1/3 : ℝ)) ^ (3:ℕ) = X := by
    rw [← Real.rpow_natCast (X ^ (1/3 : ℝ)) 3, ← Real.rpow_mul hX.le]
    norm_num
  have hXp : (0:ℝ) < X ^ (1/3 : ℝ) := Real.rpow_pos_of_pos hX _
  rw [div_pow, mul_pow]
  rw [show ((D ^ (4/3 : ℝ)) ^ 3 : ℝ) = (D ^ (4/3 : ℝ)) ^ (3:ℕ) from rfl, e1]
  rw [show ((X ^ (1/3 : ℝ)) ^ 3 : ℝ) = (X ^ (1/3 : ℝ)) ^ (3:ℕ) from rfl, e2]
  push_cast; ring

set_option maxHeartbeats 4000000 in
/-- **§3 A-decomposition** (writeup 256–267). Self-contained Nair–Roth reduction.

Threshold constant changed from the verbatim `D^{4/3}/X^{1/3}` to `D^{4/3}/(4 X^{1/3})`
(`= ½·(D⁴/(8X))^{1/3}`, still `≍ D^{4/3}/X^{1/3}`, faithful). Added regime hypotheses (all hold
for `X` large in the paper's range): `8HD ≤ X`, `1025 H ≤ D`, `64 H³ ≤ X D²`, `U ≤ H`. -/
theorem a_decomposition (P : Globals) (D : ℝ)
    (hX1 : 1 ≤ P.X) (hg : 0 < P.g) (hg' : P.g < 2 / 18977) (hu : 0 < P.u)
    (hD1 : P.H * P.X ^ (1 / 100 : ℝ) ≤ D) (hD2 : D ≤ P.X ^ (1 / 2 : ℝ))
    (hHD : 8 * P.H * D ≤ P.X) (hDlarge : 1025 * P.H ≤ D)
    (hEps : 64 * P.H ^ 3 ≤ P.X * D ^ 2) (hHU : P.U ≤ P.H) :
    ∃ C : ℝ, 0 < C ∧
      (dCard P.X P.H D : ℝ) ≤
        C * (∑ a ∈ Finset.Icc ⌈D ^ (4 / 3 : ℝ) / (4 * P.X ^ (1 / 3 : ℝ))⌉ ⌊(D / P.H) * P.U⌋,
              (DaCard P.X P.H a D : ℝ))
        + C * (P.H / P.U) := by
  refine ⟨6, by norm_num, ?_⟩
  set X := P.X with hXdef
  set H := P.H with hHdef
  set U := P.U with hUdef
  have hXpos : 0 < X := P.X_pos
  have hHpos : 0 < H := P.H_pos
  have hUpos : 0 < U := P.U_pos
  -- H ≥ 1
  have hH1 : 1 ≤ H := by
    rw [hHdef, Globals.H]
    exact Real.one_le_rpow hX1 (by linarith [hg'] : (0:ℝ) ≤ (1 - P.g) / 5)
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDlarge
  have hDX : D ^ 2 ≤ X := by
    have : D ^ 2 ≤ (X ^ (1/2:ℝ)) ^ 2 := by apply pow_le_pow_left₀ hDpos.le hD2
    rwa [← Real.rpow_natCast (X ^ (1/2:ℝ)) 2, ← Real.rpow_mul hXpos.le,
      show (1/2:ℝ) * (2:ℕ) = 1 by push_cast; ring, Real.rpow_one] at this
  have hReg4 : 4 * H ≤ D ^ 2 := by nlinarith [hDlarge, hH1, hDpos, hHpos]
  -- thresholds
  set T0 : ℝ := D ^ (4/3 : ℝ) / (4 * X ^ (1/3 : ℝ)) with hT0def
  set Du : ℝ := (D / H) * U with hDudef
  have hX3pos : (0:ℝ) < X ^ (1/3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hD43pos : (0:ℝ) < D ^ (4/3 : ℝ) := Real.rpow_pos_of_pos hDpos _
  have hT0pos : 0 < T0 := by rw [hT0def]; positivity
  have hDupos : 0 < Du := by rw [hDudef]; positivity
  -- 2*T0 = D^{4/3}/(2 X^{1/3}); (2 T0)³ = D⁴/(8X)
  have h2T0 : 2 * T0 = D ^ (4/3 : ℝ) / (2 * X ^ (1/3 : ℝ)) := by
    rw [hT0def]; field_simp; ring
  have hcube : 8 * X * (2 * T0) ^ 3 ≤ D ^ 4 := by
    rw [h2T0, thr_cube X D hXpos hDpos,
      show (8:ℝ) * X * (D ^ 4 / (8 * X)) = D ^ 4 by field_simp]
  have heps : 8 * H * (2 * T0) ≤ D ^ 2 := by
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
    have hcubeval : (2 * T0) ^ 3 = D ^ 4 / (8 * X) := by rw [h2T0, thr_cube X D hXpos hDpos]
    have hlhs : (8 * H * (2 * T0)) ^ 3 = 512 * H ^ 3 * ((2 * T0) ^ 3) := by ring
    rw [hlhs, hcubeval]
    rw [show 512 * H ^ 3 * (D ^ 4 / (8 * X)) = 64 * H ^ 3 * D ^ 4 / X by field_simp; ring]
    rw [div_le_iff₀ hXpos]
    have : 64 * H ^ 3 * D ^ 4 = (64 * H ^ 3) * D ^ 4 := by ring
    nlinarith [hEps, pow_pos hDpos 4, hXpos, sq_nonneg (D^2), pow_pos hDpos 2,
      mul_le_mul_of_nonneg_right hEps (by positivity : (0:ℝ) ≤ D ^ 4)]
  -- ============================ combinatorial layer ============================
  set lo : ℤ := ⌈D⌉ with hlodef
  set hi : ℤ := ⌊2 * D⌋ with hhidef
  -- the 𝒟-elements in range
  set S : Finset ℤ := (Finset.Icc lo hi).filter (fun d => inD X H d) with hSdef
  have hScard : (dCard X H D : ℕ) = S.card := by
    rw [Squarefree.ShortDeltaAux.dCard_eq_int]; rfl
  -- membership facts for d ∈ S
  have hSmem : ∀ d ∈ S, (D ≤ (d:ℝ) ∧ (d:ℝ) ≤ 2 * D) ∧ inD X H d := by
    intro d hd
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hlod, hdhi⟩, hinD⟩ := hd
    refine ⟨⟨?_, ?_⟩, hinD⟩
    · exact le_trans (Int.le_ceil D) (by exact_mod_cast hlod)
    · exact le_trans (by exact_mod_cast hdhi) (Int.floor_le (2 * D))
  -- the set of S-elements above `d`
  set above : ℤ → Finset ℤ := fun d => S.filter (fun e => d < e) with habovedef
  -- successor: least S-element above d (junk = d if none)
  set nxt : ℤ → ℤ := fun d => if h : (above d).Nonempty then (above d).min' h else d with hnxtdef
  -- `Sgap`: S-elements that have a strictly larger S-element
  set Sgap : Finset ℤ := S.filter (fun d => (above d).Nonempty) with hSgapdef
  set Top : Finset ℤ := S.filter (fun d => ¬ (above d).Nonempty) with hTopdef
  -- S = Sgap ⊎ Top
  have hSsplit : S.card = Sgap.card + Top.card := by
    rw [hSgapdef, hTopdef, Finset.filter_card_add_filter_neg_card_eq_card]
  -- properties of nxt on Sgap
  have hmem_above : ∀ d e : ℤ, e ∈ above d ↔ e ∈ S ∧ d < e := by
    intro d e; rw [habovedef]; exact Finset.mem_filter
  have hmem_Sgap : ∀ d : ℤ, d ∈ Sgap ↔ d ∈ S ∧ (above d).Nonempty := by
    intro d; rw [hSgapdef]; exact Finset.mem_filter
  have hnxt_eq : ∀ d : ℤ, (h : (above d).Nonempty) → nxt d = (above d).min' h := by
    intro d h; rw [hnxtdef]; simp only [h, dif_pos]
  have hnxt_mem : ∀ d ∈ Sgap, nxt d ∈ S ∧ d < nxt d ∧
      (∀ d', d < d' → d' < nxt d → ¬ inD X H d') := by
    intro d hd
    rw [hmem_Sgap] at hd
    obtain ⟨hdS, hne⟩ := hd
    have hnxteq := hnxt_eq d hne
    have hmin_mem := (above d).min'_mem hne
    rw [hmem_above] at hmin_mem
    obtain ⟨hmemS, hdlt⟩ := hmin_mem
    refine ⟨by rw [hnxteq]; exact hmemS, by rw [hnxteq]; exact hdlt, ?_⟩
    intro d' hd'1 hd'2 hd'inD
    rw [hnxteq] at hd'2
    have hdgelo : lo ≤ d := by
      rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hdS; exact hdS.1.1
    have hnxthi : (above d).min' hne ≤ hi := by
      rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hmemS; exact hmemS.1.2
    have hd'S : d' ∈ S := by
      rw [hSdef, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hd'inD⟩
    have hd'ab : d' ∈ above d := by rw [hmem_above]; exact ⟨hd'S, hd'1⟩
    have := (above d).min'_le d' hd'ab
    omega
  -- nxt strictly monotone on Sgap (hence injective)
  have hnxt_inj : Set.InjOn nxt Sgap := by
    -- strict monotonicity: c < e (both in Sgap) ⟹ nxt c < nxt e
    have hmono : ∀ c ∈ Sgap, ∀ e ∈ Sgap, c < e → nxt c < nxt e := by
      intro c hc e he hce
      obtain ⟨heS, _⟩ := (hmem_Sgap e).mp he
      obtain ⟨_, hcne⟩ := (hmem_Sgap c).mp hc
      have heab : e ∈ above c := by rw [hmem_above]; exact ⟨heS, hce⟩
      have hnxtc_le : nxt c ≤ e := by rw [hnxt_eq c hcne]; exact (above c).min'_le e heab
      obtain ⟨_, helt, _⟩ := hnxt_mem e he
      omega
    intro d hd d' hd' heq
    simp only [Finset.mem_coe] at hd hd'
    rcases lt_trichotomy d d' with h | h | h
    · exact absurd heq (ne_of_lt (hmono d hd d' hd' h))
    · exact h
    · exact absurd heq.symm (ne_of_lt (hmono d' hd' d hd h))
  -- gap function and the `inDa` membership it induces
  set gap : ℤ → ℤ := fun d => nxt d - d with hgapdef
  have hgap_pos : ∀ d ∈ Sgap, 0 < gap d := by
    intro d hd; obtain ⟨_, hlt, _⟩ := hnxt_mem d hd; simp only [hgapdef]; omega
  have hnxt_split : ∀ d : ℤ, d + gap d = nxt d := by intro d; simp only [hgapdef]; ring
  have hinDa : ∀ d ∈ Sgap, inDa X H (gap d) d := by
    intro d hd
    obtain ⟨hnxtS, hlt, hbetween⟩ := hnxt_mem d hd
    obtain ⟨⟨_, _⟩, hdinD⟩ := hSmem d ((hmem_Sgap d).mp hd).1
    refine ⟨hgap_pos d hd, hdinD, ?_, ?_⟩
    · rw [hnxt_split]
      rw [hSdef, Finset.mem_filter] at hnxtS; exact hnxtS.2
    · intro d' hd'1 hd'2
      rw [hnxt_split] at hd'2
      exact hbetween d' hd'1 hd'2
  -- range facts for `d ∈ Sgap` (in [D,2D]) and the gap bound `gap d ≤ d`
  have hSgap_range : ∀ d ∈ Sgap, D ≤ (d:ℝ) ∧ (d:ℝ) ≤ 2 * D := by
    intro d hd; exact (hSmem d ((hmem_Sgap d).mp hd).1).1
  -- ===== partition Sgap into Small / Large, then Large into Mid / Big =====
  set Small : Finset ℤ := Sgap.filter (fun d => (gap d : ℝ) ≤ T0) with hSmalldef
  set Large : Finset ℤ := Sgap.filter (fun d => ¬ (gap d : ℝ) ≤ T0) with hLargedef
  set Mid : Finset ℤ := Large.filter (fun d => (gap d : ℝ) ≤ Du) with hMiddef
  set Big : Finset ℤ := Large.filter (fun d => ¬ (gap d : ℝ) ≤ Du) with hBigdef
  have hpart1 : Sgap.card = Small.card + Large.card := by
    rw [hSmalldef, hLargedef, Finset.filter_card_add_filter_neg_card_eq_card]
  have hpart2 : Large.card = Mid.card + Big.card := by
    rw [hMiddef, hBigdef, Finset.filter_card_add_filter_neg_card_eq_card]
  -- 2 T0 = thr ≤ D
  have hD2 : (2:ℝ) ≤ D := by linarith [hDlarge, hH1]
  have hD8X : D ≤ 8 * X := by nlinarith [hDX, hD2, hXpos]
  have hthr_le_D : 2 * T0 ≤ D := by
    have hbase : (2 * T0) ^ 3 ≤ D ^ 3 := by
      rw [h2T0, thr_cube X D hXpos hDpos, div_le_iff₀ (by positivity)]
      nlinarith [hD8X, pow_pos hDpos 3, hXpos, hDpos]
    refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hDpos.le hbase
  -- tiny-gap lower bound: gap d ≥ D³/(6X) for d ∈ Sgap
  have htiny : ∀ d ∈ Sgap, D ^ 3 / (6 * X) ≤ (gap d : ℝ) := by
    intro d hd
    obtain ⟨hnxtS, hlt, _⟩ := hnxt_mem d hd
    obtain ⟨⟨hdlo, hdhi⟩, hdinD⟩ := hSmem d ((hmem_Sgap d).mp hd).1
    have hnxtinD : inD X H (d + gap d) := by
      rw [hnxt_split]; rw [hSdef, Finset.mem_filter] at hnxtS; exact hnxtS.2
    exact tiny_gap_impossible X H D (gap d) d hXpos hH1 hD2 hDX hReg4 hdlo hdhi hHD
      (hgap_pos d hd) hdinD hnxtinD
  -- ===== isolation: nxt injects Small into S \ Small =====
  have hSmall_maps : ∀ d ∈ Small, nxt d ∈ S ∧ nxt d ∉ Small := by
    intro d hd
    rw [hSmalldef, Finset.mem_filter] at hd
    obtain ⟨hdSgap, hgapd_le⟩ := hd
    obtain ⟨hnxtS, _, _⟩ := hnxt_mem d hdSgap
    refine ⟨hnxtS, ?_⟩
    intro hcontra
    rw [hSmalldef, Finset.mem_filter] at hcontra
    obtain ⟨heSgap, hgape_le⟩ := hcontra
    -- e = nxt d ∈ Sgap with gap e ≤ T0; apply isolation
    set e : ℤ := nxt d with hedef
    set a : ℤ := gap d with hadef
    set b : ℤ := gap e with hbdef
    have hapos : 0 < a := hgap_pos d hdSgap
    have hbpos : 0 < b := hgap_pos e heSgap
    have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast hapos
    have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hbpos
    obtain ⟨⟨hdlo, hdhi⟩, hdinD⟩ := hSmem d ((hmem_Sgap d).mp hdSgap).1
    -- inD facts
    have hde : d + a = e := by rw [hadef, hedef, hnxt_split]
    have heinD : inD X H (d + a) := by
      rw [hde, hedef]
      rw [hSdef, Finset.mem_filter] at hnxtS; exact hnxtS.2
    obtain ⟨henxtS, _, _⟩ := hnxt_mem e heSgap
    have hdeb : d + a + b = nxt e := by rw [hadef, hbdef, hde, hnxt_split]
    have hebinD : inD X H (d + a + b) := by
      rw [hdeb]; rw [hSdef, Finset.mem_filter] at henxtS; exact henxtS.2
    -- a+b ≤ d : (a+b ≤ 2T0 = thr ≤ D ≤ d)
    have hab_d : (a:ℝ) + (b:ℝ) ≤ (d:ℝ) := by
      have : (a:ℝ) + (b:ℝ) ≤ 2 * T0 := by rw [hadef, hbdef]; linarith [hgapd_le, hgape_le]
      linarith [this, hthr_le_D, hdlo]
    -- hab_big from tiny-gap on a and D > 1024 H
    have hab_big : 2 * H / D ^ 2 < (3 / 256 : ℝ) * X * ((a:ℝ) * (b:ℝ)) / D ^ 4 := by
      have ha_lo : D ^ 3 / (6 * X) ≤ (a:ℝ) := htiny d hdSgap
      have hbge1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast hbpos
      -- a ≥ D³/(6X) ⇒ X·a ≥ D³/6 ;  ab ≥ a
      have hXa : D ^ 3 / 6 ≤ X * (a:ℝ) := by
        rw [div_le_iff₀ (by norm_num)]
        have := (div_le_iff₀ (by positivity : (0:ℝ) < 6 * X)).mp ha_lo
        nlinarith [this, hXpos]
      have hab_ge_a : (a:ℝ) ≤ (a:ℝ) * (b:ℝ) := by nlinarith [haR, hbge1]
      -- now: (3/256)X ab/D⁴ ≥ (3/256)(D³/6)/D⁴ = D^{-1}/512;  and 2H/D² < that ⟺ 1024 H < D
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      -- 2H·D⁴ < (3/256)X ab·D²
      have hXab : D ^ 3 / 6 ≤ X * ((a:ℝ) * (b:ℝ)) := by nlinarith [hXa, hab_ge_a, hXpos]
      have hDgt : 1024 * H < D := by linarith [hDlarge, hHpos]
      nlinarith [hXab, hDgt, pow_pos hDpos 2, pow_pos hDpos 4, hHpos, hDpos,
        mul_pos (pow_pos hDpos 2) (pow_pos hDpos 4), mul_le_mul_of_nonneg_right hXab (by positivity : (0:ℝ) ≤ D ^ 2)]
    exact no_two_small_gaps X H D a b d T0 hXpos hHpos hDpos hapos hbpos hdlo hdhi hab_d
      (by rw [hadef]; exact hgapd_le) (by rw [hbdef]; exact hgape_le) hT0pos hcube heps hab_big
      hdinD heinD hebinD
  -- Small.card ≤ (S \ Small).card via the injection nxt
  have hSmall_le : Small.card ≤ (S \ Small).card := by
    apply Finset.card_le_card_of_injOn nxt
    · intro d hd
      obtain ⟨hmem, hnot⟩ := hSmall_maps d hd
      exact Finset.mem_sdiff.mpr ⟨hmem, hnot⟩
    · -- injective on Small ⊆ Sgap
      intro d hd d' hd' heq
      have hdSgap : d ∈ Sgap := by
        rw [hSmalldef, Finset.mem_coe, Finset.mem_filter] at hd; exact hd.1
      have hd'Sgap : d' ∈ Sgap := by
        rw [hSmalldef, Finset.mem_coe, Finset.mem_filter] at hd'; exact hd'.1
      exact hnxt_inj (Finset.mem_coe.mpr hdSgap) (Finset.mem_coe.mpr hd'Sgap) heq
  -- S \ Small = Large ∪ Top, disjoint, so its card = Large.card + Top.card
  have hSdiff : (S \ Small).card = Large.card + Top.card := by
    have hsub : Small ⊆ S := by
      intro d hd; rw [hSmalldef, Finset.mem_filter] at hd
      exact ((hmem_Sgap d).mp hd.1).1
    -- card (S \ Small) = card S - card Small ; and card S = card Small + card Large + card Top
    have hScard2 : S.card = Small.card + Large.card + Top.card := by
      rw [hSsplit, hpart1]
    rw [Finset.card_sdiff_of_subset hsub, hScard2]; omega
  have hTop_le : Top.card ≤ 1 := by
    -- Top ⊆ {max' S} (the unique 𝒟-max in range)
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · rw [hTopdef, hSe]; simp
    · apply le_trans (Finset.card_le_card (s := Top) (t := {S.max' hSne}) ?_)
      · simp
      · intro d hd
        rw [hTopdef, Finset.mem_filter] at hd
        obtain ⟨hdS, hdnone⟩ := hd
        rw [Finset.mem_singleton]
        by_contra hne
        have hlt : d < S.max' hSne := lt_of_le_of_ne (Finset.le_max' S d hdS) hne
        exact hdnone ⟨S.max' hSne, by rw [hmem_above]; exact ⟨Finset.max'_mem S hSne, hlt⟩⟩
  -- key card inequality:  S.card ≤ 2 Mid.card + 2 Big.card + 2
  have hScard_bound : S.card ≤ 2 * Mid.card + 2 * Big.card + 2 := by
    have h1 : S.card = Small.card + Large.card + Top.card := by rw [hSsplit, hpart1]
    have h2 : Small.card ≤ Large.card + Top.card := by rw [← hSdiff]; exact hSmall_le
    have h3 : Large.card = Mid.card + Big.card := hpart2
    omega
  -- ===== Mid block: Mid.card ≤ Σ_{a ∈ [⌈T0⌉, ⌊Du⌋]} DaCard =====
  set Asum : Finset ℤ := Finset.Icc ⌈T0⌉ ⌊Du⌋ with hAsumdef
  have hMid_facts : ∀ d ∈ Mid, d ∈ Sgap ∧ T0 < (gap d : ℝ) ∧ (gap d : ℝ) ≤ Du := by
    intro d hd
    rw [hMiddef, Finset.mem_filter, hLargedef, Finset.mem_filter] at hd
    exact ⟨hd.1.1, lt_of_not_ge hd.1.2, hd.2⟩
  have hgap_maps : ∀ d ∈ Mid, gap d ∈ Asum := by
    intro d hd
    obtain ⟨_, hgt, hle⟩ := hMid_facts d hd
    rw [hAsumdef, Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · rw [Int.ceil_le]; exact le_of_lt hgt
    · rw [Int.le_floor]; exact hle
  have hMid_card : Mid.card ≤ ∑ a ∈ Asum, (DaCard X H a D : ℝ) := by
    have hfib : (Mid.card : ℝ) = ∑ a ∈ Asum, ((Mid.filter (fun d => gap d = a)).card : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast Finset.card_eq_sum_card_fiberwise hgap_maps
    rw [hfib]
    apply Finset.sum_le_sum
    intro a ha
    -- fiber ⊆ DaCard-filter
    have hsub : Mid.filter (fun d => gap d = a) ⊆
        (Finset.Icc lo hi).filter (fun d => inDa X H a d) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      obtain ⟨hdMid, hga⟩ := hd
      obtain ⟨hdSgap, _, _⟩ := hMid_facts d hdMid
      rw [Finset.mem_filter]
      have hdS := ((hmem_Sgap d).mp hdSgap).1
      rw [hSdef, Finset.mem_filter] at hdS
      refine ⟨hdS.1, ?_⟩
      have := hinDa d hdSgap
      rwa [hga] at this
    have hcard_le : (Mid.filter (fun d => gap d = a)).card ≤
        ((Finset.Icc lo hi).filter (fun d => inDa X H a d)).card :=
      Finset.card_le_card hsub
    have hDaeq : DaCard X H a D = ((Finset.Icc lo hi).filter (fun d => inDa X H a d)).card := by
      rw [DaCard, hlodef, hhidef]
    rw [hDaeq]; exact_mod_cast hcard_le
  -- ===== Big block: Big.card ≤ H/U + 1 via separation =====
  have hBig_facts : ∀ d ∈ Big, d ∈ Sgap ∧ Du < (gap d : ℝ) := by
    intro d hd
    rw [hBigdef, Finset.mem_filter, hLargedef, Finset.mem_filter] at hd
    exact ⟨hd.1.1, lt_of_not_ge hd.2⟩
  have hBig_card : (Big.card : ℝ) ≤ H / U + 1 := by
    -- separation
    have hsep : ∀ d ∈ Big, ∀ d' ∈ Big, d < d' → Du < (d' : ℝ) - d := by
      intro d hd d' hd' hlt
      obtain ⟨hdSgap, hgapd⟩ := hBig_facts d hd
      have hd'S : d' ∈ S := by
        obtain ⟨hd'Sgap, _⟩ := hBig_facts d' hd'
        exact ((hmem_Sgap d').mp hd'Sgap).1
      have hd'ab : d' ∈ above d := by rw [hmem_above]; exact ⟨hd'S, hlt⟩
      obtain ⟨_, _, hdnone⟩ := hnxt_mem d hdSgap
      have hnxtd_le : nxt d ≤ d' := by
        rw [hnxt_eq d ((hmem_Sgap d).mp hdSgap).2]; exact (above d).min'_le d' hd'ab
      -- nxt d = d + gap d > d + Du
      have : (d:ℝ) + Du < (nxt d : ℝ) := by
        rw [← hnxt_split d]; push_cast; linarith [hgapd]
      have hle : (nxt d : ℝ) ≤ (d':ℝ) := by exact_mod_cast hnxtd_le
      linarith
    have hsub : ∀ d ∈ Big, lo ≤ d ∧ d ≤ hi := by
      intro d hd
      obtain ⟨hdSgap, _⟩ := hBig_facts d hd
      have := ((hmem_Sgap d).mp hdSgap).1
      rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at this
      exact this.1
    have hlohi : (lo : ℝ) ≤ hi := by
      have hlo1 : (lo:ℝ) < D + 1 := by rw [hlodef]; exact Int.ceil_lt_add_one D
      have hhi1 : 2 * D - 1 < (hi:ℝ) := by rw [hhidef]; exact Int.sub_one_lt_floor (2 * D)
      linarith [hD2]
    have hbound := sep_card_bound Big lo hi Du hDupos hlohi hsub hsep
    -- (hi - lo)/Du ≤ H/U
    have hkey : ((hi:ℝ) - lo) / Du ≤ H / U := by
      have h1 : D ≤ (lo:ℝ) := Int.le_ceil D
      have h2 : (hi:ℝ) ≤ 2 * D := Int.floor_le (2 * D)
      have hnum : (hi:ℝ) - lo ≤ D := by linarith
      have hDuD : Du = (D / H) * U := hDudef
      rw [hDuD, div_le_div_iff₀ (by positivity) hUpos]
      have : ((hi:ℝ) - lo) * U ≤ D * U := by
        apply mul_le_mul_of_nonneg_right hnum hUpos.le
      -- goal: (hi-lo)*U ≤ H * ((D/H)*U) = D*U
      rw [show H * (D / H * U) = D * U by field_simp]
      exact this
    linarith [hbound, hkey]
  -- ===== final assembly =====
  have hSumnn : (0:ℝ) ≤ ∑ a ∈ Asum, (DaCard X H a D : ℝ) := by
    apply Finset.sum_nonneg; intro a _; positivity
  have hHU1 : (1:ℝ) ≤ H / U := by
    rw [le_div_iff₀ hUpos]; linarith [hHU]
  -- cast the card bound to ℝ
  have hScard_R : (S.card : ℝ) ≤ 2 * (Mid.card : ℝ) + 2 * (Big.card : ℝ) + 2 := by
    exact_mod_cast hScard_bound
  -- goal sum = Asum sum (definitional via set)
  rw [show (dCard X H D : ℝ) = (S.card : ℝ) by rw [hScard]]
  calc (S.card : ℝ) ≤ 2 * (Mid.card : ℝ) + 2 * (Big.card : ℝ) + 2 := hScard_R
    _ ≤ 2 * (∑ a ∈ Asum, (DaCard X H a D : ℝ)) + 2 * (H / U + 1) + 2 := by
        gcongr
    _ ≤ 6 * (∑ a ∈ Asum, (DaCard X H a D : ℝ)) + 6 * (H / U) := by
        nlinarith [hSumnn, hHU1]

end Squarefree
