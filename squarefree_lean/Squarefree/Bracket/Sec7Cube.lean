import Squarefree.Bracket.BoxPowerSums

/-!
# §7 averaged popular cube (plan node N5) — Phase-1b-β SIGNATURE ONLY

md 1463–1487 (Lemma 7.2): the averaged form of the threefold Lemma-2.2 differencing
argument over the rectangular shift box `1 ≤ h₁ ≤ ⌊W⌋, 1 ≤ h₂ ≤ ⌊W²⌋, 1 ≤ h₃ ≤ ⌊W⁴⌋`
(= `box W` of `BoxPowerSums`).  Stated self-contained over an abstract popular set
`E ⊆ Finset ℤ` (no in-tree 3-fold Lemma 2.2 exists; `Counting/FourthDeriv.lean`'s popular
cube is single-witness, not averaged).  The conclusion sums `#E₃` over `box W`, the shape
the N15/N22 harvests compare against (`Σ ≤ (R/W)/sec7_harvM`).

## Constant ledger additions (absolute constants; tools/sec7_ledger.py)
* `sec7_cCubeIn = 10³` — hypothesis-side margin: md 1460 assumes the bare `M := #E > R/W`;
  the iterated Cauchy–Schwarz of the averaged differencing needs a fixed margin
  `#E ≥ sec7_cCubeIn·R/W` (each of the three levels spends a factor; ≥ 16 suffices,
  10³ generous).  Absorbed into prop_7_1's constant at N23 (the contradiction dichotomy:
  either `M ≤ sec7_cCubeIn·R/W` — done — or N5 + harvest contradict).
* `sec7_cCube = 10²` — the `≫`-constant of md 1478: conclusion `Σ ≥ (R/W)/sec7_cCube`.
  N23 needs `sec7_cCube < sec7_harvM = 10³` ✓.
-/

open Classical Finset

namespace Squarefree

/-- Hypothesis-side margin of the N5 averaged-cube lower bound (md 1460 `#E > R/W`,
formal margin; ledger). -/
def sec7_cCubeIn : ℝ := 10 ^ 3

/-- The `≫`-constant of the N5 conclusion (md 1473–78; ledger). -/
def sec7_cCube : ℝ := 10 ^ 2

theorem sec7_cCubeIn_pos : (0:ℝ) < sec7_cCubeIn := by norm_num [sec7_cCubeIn]
theorem sec7_cCube_pos : (0:ℝ) < sec7_cCube := by norm_num [sec7_cCube]

/- md 1467–1471: "E_3(h_1,h_2,h_3) := {r : r+ε₁h₁+ε₂h₂+ε₃h₃ ∈ E for all ε_i ∈ {0,1}}". -/
/-- **`E₃(h₁,h₂,h₃)`** (md 1467–71): the eight-corner cube set of `E`. -/
noncomputable def sec7_cubeSet (E : Finset ℤ) (h₁ h₂ h₃ : ℕ) : Finset ℤ :=
  E.filter (fun r => ∀ ε₁ ε₂ ε₃ : ℕ, ε₁ ≤ 1 → ε₂ ≤ 1 → ε₃ ≤ 1 →
    r + ε₁ * (h₁ : ℤ) + ε₂ * (h₂ : ℤ) + ε₃ * (h₃ : ℤ) ∈ E)

/-! ### Generic single-level block-Cauchy–Schwarz machinery (A2 gate route)

`diff_sum_lower`: for `E` inside a window of length `≤ N` and any `1 ≤ H ≤ N`,
`Σ_{1≤h≤H} #(E ∩ (E−h)) ≥ #E²·H/(4N) − #E` — blocks of length `H`, Cauchy–Schwarz over
the `≤ 2N/H` blocks, within-block ordered pairs have difference in `[0, H−1]`. -/

/-- For `x ≥ 1`, `x ≤ 2⌊x⌋₊`. -/
private lemma le_two_mul_floor {x : ℝ} (hx : 1 ≤ x) : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
  have h1 : (1 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h1' : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
  have h2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  linarith

/-- Ordered-pair count: `#s² ≤ 2 Σ_{x∈s} #{y ∈ s : x ≤ y}`. -/
private lemma sq_card_le (s : Finset ℤ) :
    s.card ^ 2 ≤ 2 * ∑ x ∈ s, (s.filter fun y => x ≤ y).card := by
  have hswap : ∑ x ∈ s, (s.filter fun y => y ≤ x).card
      = ∑ x ∈ s, (s.filter fun y => x ≤ y).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hcover : ∀ x ∈ s, s.card ≤
      (s.filter fun y => x ≤ y).card + (s.filter fun y => y ≤ x).card := by
    intro x _
    have hsub : (s.filter fun y => ¬ x ≤ y) ⊆ s.filter fun y => y ≤ x := by
      intro y hy
      rw [Finset.mem_filter] at hy ⊢
      exact ⟨hy.1, le_of_not_ge hy.2⟩
    calc s.card = ((s.filter fun y => x ≤ y) ∪ s.filter fun y => ¬ x ≤ y).card := by
          rw [Finset.filter_union_filter_not_eq]
      _ ≤ (s.filter fun y => x ≤ y).card + (s.filter fun y => ¬ x ≤ y).card :=
          Finset.card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (Finset.card_le_card hsub) _
  calc s.card ^ 2 = ∑ _x ∈ s, s.card := by rw [Finset.sum_const, smul_eq_mul, sq]
    _ ≤ ∑ x ∈ s, ((s.filter fun y => x ≤ y).card + (s.filter fun y => y ≤ x).card) :=
        Finset.sum_le_sum hcover
    _ = ∑ x ∈ s, (s.filter fun y => x ≤ y).card
        + ∑ x ∈ s, (s.filter fun y => y ≤ x).card := Finset.sum_add_distrib
    _ = 2 * ∑ x ∈ s, (s.filter fun y => x ≤ y).card := by rw [hswap]; ring

/-- Within the block of `x` (length-`H` blocks based at `a`), the elements `y ≥ x` of `E`
inject into the shifts `d ∈ [0, H−1]` with `x + d ∈ E`. -/
private lemma block_filter_le (E : Finset ℤ) (a : ℤ) {H : ℤ} (hH : 0 < H) (x : ℤ) :
    ((E.filter fun y => (y - a) / H = (x - a) / H).filter fun y => x ≤ y).card ≤
      ((Finset.Icc 0 (H - 1)).filter fun d => x + d ∈ E).card := by
  apply Finset.card_le_card_of_injOn (fun y => y - x)
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hy ⊢
    obtain ⟨⟨hyE, hdiv⟩, hxy⟩ := hy
    have e1 := Int.mul_ediv_add_emod (y - a) H
    have e2 := Int.mul_ediv_add_emod (x - a) H
    have m1 : 0 ≤ (x - a) % H := Int.emod_nonneg _ hH.ne'
    have m2 : (y - a) % H < H := Int.emod_lt_of_pos _ hH
    rw [hdiv] at e1
    have hlt : y - x < H := by linarith
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show x + (y - x) = y by ring]
    exact hyE
  · exact fun y₁ _ y₂ _ h => sub_left_inj.mp h

/-- Summed over the fibers (blocks) of `x ↦ (x−a)/H`, the squared fiber counts are
bounded by twice the total shifted-intersection count over `d ∈ [0, H−1]`. -/
private lemma fiber_sq_le (E : Finset ℤ) (a : ℤ) {H : ℤ} (hH : 0 < H)
    {J : Finset ℤ} (hmaps : ∀ x ∈ E, (x - a) / H ∈ J) :
    ∑ j ∈ J, (E.filter fun x => (x - a) / H = j).card ^ 2 ≤
      2 * ∑ d ∈ Finset.Icc 0 (H - 1), (E.filter fun x => x + d ∈ E).card := by
  calc ∑ j ∈ J, (E.filter fun x => (x - a) / H = j).card ^ 2
      ≤ ∑ j ∈ J, 2 * ∑ x ∈ E.filter fun x => (x - a) / H = j,
          ((E.filter fun y => (y - a) / H = (x - a) / H).filter fun y => x ≤ y).card := by
        refine Finset.sum_le_sum fun j _ => le_trans (sq_card_le _) ?_
        apply Nat.le_of_eq
        congr 1
        exact Finset.sum_congr rfl fun x hx => by
          simp only [(Finset.mem_filter.mp hx).2]
    _ = 2 * ∑ x ∈ E,
          ((E.filter fun y => (y - a) / H = (x - a) / H).filter fun y => x ≤ y).card := by
        rw [← Finset.mul_sum, Finset.sum_fiberwise_of_maps_to hmaps]
    _ ≤ 2 * ∑ x ∈ E, ((Finset.Icc 0 (H - 1)).filter fun d => x + d ∈ E).card :=
        Nat.mul_le_mul_left 2 (Finset.sum_le_sum fun x _ => block_filter_le E a hH x)
    _ = 2 * ∑ d ∈ Finset.Icc 0 (H - 1), (E.filter fun x => x + d ∈ E).card := by
        congr 1
        simp only [Finset.card_filter]
        exact Finset.sum_comm

/-- **Single-level block-Cauchy–Schwarz** (A2 gate route): if `E ⊆ [a,b]` with
`b − a + 1 ≤ N` and `1 ≤ H ≤ N`, then
`Σ_{1≤h≤H} #(E ∩ (E−h)) ≥ #E²·H/(4N) − #E`. -/
private lemma diff_sum_lower (E : Finset ℤ) {a b : ℤ} (hE : E ⊆ Finset.Icc a b)
    {H : ℕ} (hH : 1 ≤ H) {N : ℝ} (hab : (b : ℝ) - a + 1 ≤ N) (hHN : (H : ℝ) ≤ N) :
    (E.card : ℝ) ^ 2 * H / (4 * N) - E.card ≤
      ∑ h ∈ Finset.Icc 1 H, ((E.filter fun x => x + (h : ℤ) ∈ E).card : ℝ) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le hH0 hHN
  set T : ℝ := ∑ h ∈ Finset.Icc 1 H, ((E.filter fun x => x + (h : ℤ) ∈ E).card : ℝ)
    with hTdef
  have hTnn : (0 : ℝ) ≤ T :=
    Finset.sum_nonneg fun _ _ => by positivity
  rcases E.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp [hTdef]
  have hax := Finset.mem_Icc.mp (hE hx₀)
  set H' : ℤ := (H : ℤ) with hH'def
  have hH'0 : 0 < H' := by omega
  set m : ℤ := (b - a) / H' with hmdef
  have hm0 : 0 ≤ m := Int.ediv_nonneg (by omega) hH'0.le
  have hmaps : ∀ x ∈ E, (x - a) / H' ∈ Finset.Icc 0 m := by
    intro x hx
    have hx' := Finset.mem_Icc.mp (hE hx)
    rw [Finset.mem_Icc]
    exact ⟨Int.ediv_nonneg (by omega) hH'0.le, Int.ediv_le_ediv hH'0 (by omega)⟩
  -- Cauchy–Schwarz over the blocks
  have hCS : (E.card : ℝ) ^ 2 ≤ ((Finset.Icc 0 m).card : ℝ) *
      ∑ j ∈ Finset.Icc 0 m, ((E.filter fun x => (x - a) / H' = j).card : ℝ) ^ 2 := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast
    exact sq_sum_le_card_mul_sum_sq
  -- split off d = 0 and reindex the shifted counts to ℕ
  have hsplit : ∑ d ∈ Finset.Icc (0 : ℤ) (H' - 1), (E.filter fun x => x + d ∈ E).card ≤
      E.card + ∑ h ∈ Finset.Icc 1 H, (E.filter fun x => x + (h : ℤ) ∈ E).card := by
    have h0mem : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) (H' - 1) :=
      Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩
    rw [← Finset.sum_erase_add _ _ h0mem]
    have herase : (Finset.Icc (0 : ℤ) (H' - 1)).erase 0 = Finset.Icc 1 (H' - 1) := by
      ext d; simp only [Finset.mem_erase, Finset.mem_Icc]; omega
    have h0 : (E.filter fun x => x + (0 : ℤ) ∈ E).card = E.card := by
      simp [Finset.filter_true_of_mem]
    rw [herase, h0, add_comm]
    apply Nat.add_le_add_left
    have himg : Finset.Icc (1 : ℤ) (H' - 1)
        = (Finset.Icc 1 (H - 1)).image (fun n : ℕ => (n : ℤ)) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_image]
      constructor
      · intro hd; exact ⟨d.toNat, by omega, by omega⟩
      · rintro ⟨n, hn, rfl⟩; omega
    rw [himg, Finset.sum_image fun n _ k _ h => Nat.cast_injective h]
    exact Finset.sum_le_sum_of_subset (Finset.Icc_subset_Icc_right (by omega))
  -- block count
  have hJc : ((Finset.Icc 0 m).card : ℝ) * H ≤ 2 * N := by
    have hcard : ((Finset.Icc 0 m).card : ℝ) = (m : ℝ) + 1 := by
      rw [Int.card_Icc, sub_zero]
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ m + 1)
    have hHm : H' * m ≤ b - a := by
      have e := Int.mul_ediv_add_emod (b - a) H'
      have r := Int.emod_nonneg (b - a) hH'0.ne'
      rw [← hmdef] at e
      linarith
    have hHmR : (H : ℝ) * m ≤ (b : ℝ) - a := by exact_mod_cast hHm
    rw [hcard]
    nlinarith
  -- assemble
  have hcomb : ∑ j ∈ Finset.Icc 0 m, (E.filter fun x => (x - a) / H' = j).card ^ 2 ≤
      2 * (E.card + ∑ h ∈ Finset.Icc 1 H, (E.filter fun x => x + (h : ℤ) ∈ E).card) :=
    le_trans (fiber_sq_le E a hH'0 hmaps) (Nat.mul_le_mul_left 2 hsplit)
  have hcombR : ∑ j ∈ Finset.Icc 0 m, ((E.filter fun x => (x - a) / H' = j).card : ℝ) ^ 2 ≤
      2 * ((E.card : ℝ) + T) := by
    rw [hTdef]
    exact_mod_cast hcomb
  have hsqnn : (0 : ℝ) ≤
      ∑ j ∈ Finset.Icc 0 m, ((E.filter fun x => (x - a) / H' = j).card : ℝ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hJle : ((Finset.Icc 0 m).card : ℝ) ≤ 2 * N / H := by
    rw [le_div_iff₀ hH0]; exact hJc
  have key : (E.card : ℝ) ^ 2 ≤ (2 * N / H) * (2 * ((E.card : ℝ) + T)) :=
    le_trans hCS (mul_le_mul hJle hcombR hsqnn (by positivity))
  have hmulH := mul_le_mul_of_nonneg_right key hH0.le
  have hident : (2 * N / H) * (2 * ((E.card : ℝ) + T)) * H
      = 4 * N * ((E.card : ℝ) + T) := by
    field_simp
    ring
  rw [hident] at hmulH
  rw [sub_le_iff_le_add, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * N)]
  linarith

/-- Single level specialized to the §7 window `[⌈R/72⌉, ⌊16R⌋]` (length `≤ 16R`) and
edge `H = ⌊W^k⌋₊ ≥ W^k/2`, `k ≤ 8`: the `1/(4·16·2) = 1/128` budget. -/
private lemma level_step {R W : ℝ} (hW : 1 ≤ W) (hRW : W ^ 8 ≤ R) {k : ℕ} (hk : k ≤ 8)
    (F : Finset ℤ) (hF : F ⊆ Finset.Icc ⌈R / 72⌉ ⌊16 * R⌋) :
    (F.card : ℝ) ^ 2 * (W ^ k / (128 * R)) - F.card ≤
      ∑ h ∈ Finset.Icc 1 ⌊W ^ k⌋₊, ((F.filter fun x => x + (h : ℤ) ∈ F).card : ℝ) := by
  have hWk1 : (1 : ℝ) ≤ W ^ k := one_le_pow₀ hW
  have hR1 : (1 : ℝ) ≤ R := le_trans (one_le_pow₀ hW) hRW
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hfl1 : 1 ≤ ⌊W ^ k⌋₊ := Nat.le_floor (by exact_mod_cast hWk1)
  have hflle : (⌊W ^ k⌋₊ : ℝ) ≤ W ^ k := Nat.floor_le (by positivity)
  have hhalf : W ^ k ≤ 2 * (⌊W ^ k⌋₊ : ℝ) := le_two_mul_floor hWk1
  have hab : (⌊16 * R⌋ : ℝ) - ⌈R / 72⌉ + 1 ≤ 16 * R := by
    have h1 : (⌊16 * R⌋ : ℝ) ≤ 16 * R := Int.floor_le _
    have h2 : (1 : ℝ) ≤ (⌈R / 72⌉ : ℝ) := by
      exact_mod_cast Int.ceil_pos.mpr (by positivity : (0 : ℝ) < R / 72)
    linarith
  have hWkR : W ^ k ≤ R := le_trans (pow_le_pow_right₀ hW hk) hRW
  have hHN : ((⌊W ^ k⌋₊ : ℕ) : ℝ) ≤ 16 * R := by linarith
  refine le_trans ?_ (diff_sum_lower F hF hfl1 hab hHN)
  rw [sub_le_sub_iff_right]
  have hcard : (0 : ℝ) ≤ (F.card : ℝ) ^ 2 := sq_nonneg _
  calc (F.card : ℝ) ^ 2 * (W ^ k / (128 * R)) = (F.card : ℝ) ^ 2 * W ^ k / (128 * R) := by
        ring
    _ ≤ (F.card : ℝ) ^ 2 * (2 * (⌊W ^ k⌋₊ : ℝ)) / (128 * R) := by
        gcongr
    _ = (F.card : ℝ) ^ 2 * (⌊W ^ k⌋₊ : ℝ) / (4 * (16 * R)) := by ring

/-- Aggregation across an index set: per-index quadratic lower bounds plus
Cauchy–Schwarz over the (≤ `c`) indices. -/
private lemma agg_sum {ι : Type*} {s : Finset ι} {f g : ι → ℝ} {K c : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (hcard : (s.card : ℝ) ≤ c)
    (h : ∀ i ∈ s, f i ^ 2 * K - f i ≤ g i) :
    (∑ i ∈ s, f i) ^ 2 * (K / c) - ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i := by
  have hsq : (0 : ℝ) ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : (∑ i ∈ s, f i) ^ 2 ≤ c * ∑ i ∈ s, f i ^ 2 :=
    le_trans sq_sum_le_card_mul_sum_sq (mul_le_mul_of_nonneg_right hcard hsq)
  have h2 : ∑ i ∈ s, (f i ^ 2 * K - f i) ≤ ∑ i ∈ s, g i := Finset.sum_le_sum h
  have h3 : ∑ i ∈ s, (f i ^ 2 * K - f i) = (∑ i ∈ s, f i ^ 2) * K - ∑ i ∈ s, f i := by
    rw [Finset.sum_sub_distrib, Finset.sum_mul]
  have h4 : (∑ i ∈ s, f i) ^ 2 * (K / c) ≤ (∑ i ∈ s, f i ^ 2) * K := by
    calc (∑ i ∈ s, f i) ^ 2 * (K / c) = (∑ i ∈ s, f i) ^ 2 * K / c := by ring
      _ ≤ c * (∑ i ∈ s, f i ^ 2) * K / c := by
          gcongr
      _ = (∑ i ∈ s, f i ^ 2) * K := by field_simp
  linarith

/-- One step of the quadratic growth chain: from `c ≤ x·β` and `y ≥ x²β − x` deduce
`c(c−1) ≤ y·β`. -/
private lemma agg {β x y c : ℝ} (hβ : 0 < β) (hc : 2 ≤ c) (hx : c ≤ x * β)
    (h : x ^ 2 * β - x ≤ y) : c * (c - 1) ≤ y * β := by
  nlinarith [mul_le_mul_of_nonneg_right h hβ.le,
    mul_nonneg (sub_nonneg.mpr hx) (by linarith : (0 : ℝ) ≤ x * β + c - 1)]

/-- First difference set `E ∩ (E − h₁)`. -/
private def dE1 (E : Finset ℤ) (h₁ : ℕ) : Finset ℤ := E.filter fun x => x + (h₁ : ℤ) ∈ E

/-- Second difference set: the four-corner set. -/
private def dE2 (E : Finset ℤ) (h₁ h₂ : ℕ) : Finset ℤ :=
  (dE1 E h₁).filter fun x => x + (h₂ : ℤ) ∈ dE1 E h₁

/-- Third difference set: the eight-corner set, iterated form. -/
private def dE3 (E : Finset ℤ) (h₁ h₂ h₃ : ℕ) : Finset ℤ :=
  (dE2 E h₁ h₂).filter fun x => x + (h₃ : ℤ) ∈ dE2 E h₁ h₂

/-- The iterated triple-difference set sits inside the `∀ ε`-form cube set. -/
private lemma dE3_subset (E : Finset ℤ) (h₁ h₂ h₃ : ℕ) :
    dE3 E h₁ h₂ h₃ ⊆ sec7_cubeSet E h₁ h₂ h₃ := by
  intro r hr
  simp only [dE3, dE2, dE1, Finset.mem_filter] at hr
  obtain ⟨⟨⟨h000, h100⟩, h010, h110⟩, ⟨h001, h101⟩, h011, h111⟩ := hr
  have h110' : r + (h₁ : ℤ) + h₂ ∈ E := by rwa [add_right_comm] at h110
  have h101' : r + (h₁ : ℤ) + h₃ ∈ E := by rwa [add_right_comm] at h101
  have h011' : r + (h₂ : ℤ) + h₃ ∈ E := by rwa [add_right_comm] at h011
  have h111' : r + (h₁ : ℤ) + h₂ + h₃ ∈ E := by
    rw [show r + (h₁ : ℤ) + h₂ + h₃ = r + h₃ + h₂ + h₁ by ring]; exact h111
  simp only [sec7_cubeSet, Finset.mem_filter]
  refine ⟨h000, ?_⟩
  intro ε₁ ε₂ ε₃ hε₁ hε₂ hε₃
  interval_cases ε₁ <;> interval_cases ε₂ <;> interval_cases ε₃ <;>
    simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero] <;>
    assumption

/- N5 (md 1463–1487, Lemma 7.2): "For integer shifts 1 ≤ h₁ ≤ ⌊W⌋, 1 ≤ h₂ ≤ ⌊W²⌋,
   1 ≤ h₃ ≤ ⌊W⁴⌋ … Then  Σ_{h₁≤W} Σ_{h₂≤W²} Σ_{h₃≤W⁴} |E₃(h₁,h₂,h₃)| ≫ R/W.
   This is the averaged form of the threefold Lemma 2.2 differencing argument. … It gives
   the displayed lower bound for the total number of eight-corner cubes in the whole
   rectangular shift box.  No lower bound on any individual product h₁h₂h₃ is used."
   Context md 1454–60: "E := {r ≍ R : ‖g_j(r)‖ ≤ δ₀}.  Assume M := #E > R/W."  Here E enters
   abstractly (any E ⊆ [⌈R/72⌉,⌊16R⌋] ∩ ℤ — the AM-2 WIDE `RaWitness` window); the side
   condition `W⁸ ≤ R` is the §4.3/N18 one (md 1870–1911), needed so the box reaches into
   the interval.
   UNCERTAINTY: md's hypothesis is the bare `M > R/W`; the formal margin `sec7_cCubeIn` is
   required for the three-level Cauchy–Schwarz (bare `> R/W` admits Σ ≈ R/W⁸ near-misses);
   N23 absorbs it in prop_7_1's constant.  Revisit constants at Phase-2 audit. -/
/-- **N5 = Lemma 7.2** (md 1463–1487; AM-2 wide window): averaged popular-cube lower
bound — if `#E ≥ sec7_cCubeIn·R/W` on `[R/72,16R]` then the total eight-corner cube count
over the rectangular shift box is `≥ (R/W)/sec7_cCube`. -/
theorem sec7_averaged_cube_lower {R W : ℝ} (hW : 1 ≤ W) (hRW : W ^ 8 ≤ R)
    (E : Finset ℤ) (hE : E ⊆ Finset.Icc ⌈R / 72⌉ ⌊16 * R⌋)
    (hM : sec7_cCubeIn * (R / W) ≤ (E.card : ℝ)) :
    R / (W * sec7_cCube) ≤
      ∑ p ∈ box W, ((sec7_cubeSet E p.1 p.2.1 p.2.2).card : ℝ) := by
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le one_pos hW
  have hR1 : (1 : ℝ) ≤ R := le_trans (one_le_pow₀ hW) hRW
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  set β : ℝ := W / (128 * R) with hβdef
  have hβ : 0 < β := by positivity
  have hk28 : (2 : ℕ) ≤ 8 := by norm_num
  have hk48 : (4 : ℕ) ≤ 8 := by norm_num
  have hsub1 : ∀ h₁ : ℕ, dE1 E h₁ ⊆ Finset.Icc ⌈R / 72⌉ ⌊16 * R⌋ :=
    fun h₁ => (Finset.filter_subset _ _).trans hE
  have hsub2 : ∀ h₁ h₂ : ℕ, dE2 E h₁ h₂ ⊆ Finset.Icc ⌈R / 72⌉ ⌊16 * R⌋ :=
    fun h₁ h₂ => (Finset.filter_subset _ _).trans (hsub1 h₁)
  set S₁ : ℝ := ∑ h₁ ∈ Finset.Icc 1 ⌊W⌋₊, ((dE1 E h₁).card : ℝ) with hS₁
  set S₂ : ℝ := ∑ q ∈ Finset.Icc 1 ⌊W⌋₊ ×ˢ Finset.Icc 1 ⌊W ^ 2⌋₊,
      ((dE2 E q.1 q.2).card : ℝ) with hS₂
  set S₃ : ℝ := ∑ q ∈ Finset.Icc 1 ⌊W⌋₊ ×ˢ Finset.Icc 1 ⌊W ^ 2⌋₊,
      ∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, ((dE3 E q.1 q.2 h₃).card : ℝ) with hS₃
  -- Level 1: difference by h₁ over E
  have l1 : (E.card : ℝ) ^ 2 * β - E.card ≤ S₁ := by
    have h := level_step hW hRW (k := 1) (by norm_num) E hE
    simpa only [pow_one, hS₁, hβdef, dE1] using h
  -- Level 2: difference each E₁(h₁) by h₂, Cauchy–Schwarz over h₁
  have l2 : S₁ ^ 2 * β - S₁ ≤ S₂ := by
    have hcardA : ((Finset.Icc 1 ⌊W⌋₊).card : ℝ) ≤ W := by
      simpa [Nat.card_Icc] using Nat.floor_le hW0.le
    have hagg := agg_sum (f := fun h₁ => ((dE1 E h₁).card : ℝ))
      (g := fun h₁ => ∑ h₂ ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, ((dE2 E h₁ h₂).card : ℝ))
      (K := W ^ 2 / (128 * R)) (by positivity) hW0 hcardA
      (fun h₁ _ => by
        have h := level_step hW hRW (k := 2) hk28 (dE1 E h₁) (hsub1 h₁)
        simpa only [dE2] using h)
    have hKc : W ^ 2 / (128 * R) / W = β := by rw [hβdef]; field_simp
    rw [hKc, ← hS₁] at hagg
    rw [hS₂, Finset.sum_product]
    exact hagg
  -- Level 3: difference each E₂(h₁,h₂) by h₃, Cauchy–Schwarz over (h₁,h₂)
  have l3 : S₂ ^ 2 * β - S₂ ≤ S₃ := by
    have hcardAB : (((Finset.Icc 1 ⌊W⌋₊ ×ˢ Finset.Icc 1 ⌊W ^ 2⌋₊).card : ℕ) : ℝ) ≤ W ^ 3 := by
      rw [Finset.card_product]
      push_cast
      simp only [Nat.card_Icc, Nat.add_sub_cancel]
      calc (⌊W⌋₊ : ℝ) * (⌊W ^ 2⌋₊ : ℝ) ≤ W * W ^ 2 := by
            have h1 : (⌊W⌋₊ : ℝ) ≤ W := Nat.floor_le hW0.le
            have h2 : (⌊W ^ 2⌋₊ : ℝ) ≤ W ^ 2 := Nat.floor_le (by positivity)
            exact mul_le_mul h1 h2 (by positivity) hW0.le
        _ = W ^ 3 := by ring
    have hagg := agg_sum (f := fun q : ℕ × ℕ => ((dE2 E q.1 q.2).card : ℝ))
      (g := fun q : ℕ × ℕ => ∑ h₃ ∈ Finset.Icc 1 ⌊W ^ 4⌋₊, ((dE3 E q.1 q.2 h₃).card : ℝ))
      (K := W ^ 4 / (128 * R)) (by positivity) (by positivity) hcardAB
      (fun q _ => by
        have h := level_step hW hRW (k := 4) hk48 (dE2 E q.1 q.2) (hsub2 q.1 q.2)
        simpa only [dE3] using h)
    have hKc : W ^ 4 / (128 * R) / W ^ 3 = β := by rw [hβdef]; field_simp
    rw [hKc, ← hS₂, ← hS₃] at hagg
    exact hagg
  -- the quadratic growth chain (sympy: 7 → 42 → 1722 → 2963562 ≥ 1/12800)
  have c0 : (7 : ℝ) ≤ (E.card : ℝ) * β := by
    have hMβ := mul_le_mul_of_nonneg_right hM hβ.le
    have hc : sec7_cCubeIn = 1000 := by norm_num [sec7_cCubeIn]
    have he : sec7_cCubeIn * (R / W) * β = 1000 / 128 := by
      rw [hβdef, hc]; field_simp
    rw [he] at hMβ
    linarith
  have a1 : (42 : ℝ) ≤ S₁ * β := by
    have h := agg hβ (by norm_num) c0 l1; norm_num at h; exact h
  have a2 : (1722 : ℝ) ≤ S₂ * β := by
    have h := agg hβ (by norm_num) a1 l2; norm_num at h; exact h
  have a3 : (2963562 : ℝ) ≤ S₃ * β := by
    have h := agg hβ (by norm_num) a2 l3; norm_num at h; exact h
  -- compare with the cube-set box sum and conclude
  have hbox : S₃ ≤ ∑ p ∈ box W, ((sec7_cubeSet E p.1 p.2.1 p.2.2).card : ℝ) := by
    rw [hS₃]
    simp only [box, Finset.sum_product]
    refine Finset.sum_le_sum fun h₁ _ => Finset.sum_le_sum fun h₂ _ =>
      Finset.sum_le_sum fun h₃ _ => ?_
    exact_mod_cast Finset.card_le_card (dE3_subset E h₁ h₂ h₃)
  have hfin : R / (W * sec7_cCube) * β ≤ S₃ * β := by
    have hc : sec7_cCube = 100 := by norm_num [sec7_cCube]
    have he : R / (W * sec7_cCube) * β = 1 / 12800 := by
      rw [hβdef, hc]; field_simp; ring
    rw [he]; linarith
  exact le_trans (le_of_mul_le_mul_right hfin hβ) hbox

end Squarefree
