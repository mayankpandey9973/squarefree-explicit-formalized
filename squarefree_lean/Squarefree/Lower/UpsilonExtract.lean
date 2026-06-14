import Squarefree.Lower.DefectUpsilon
import Squarefree.Lower.UpsilonNearInt

/-!
# §5 Step-4 integer extraction (writeup 1033–1043)

In the large-defect range `|v| ≥ V₂` the near-integer quantity `Υ` rounds to a **nonzero**
integer `s` with `1 ≤ |s| ≪ G⁵U³⁵/Ω⁸`.  Concretely, writing

* `Lval := (Xa/d⁵)·((−4+10a/d)·(p₁+p₂/d))`  the leading cubic/quartic value
  (`Upsilon_expand`'s main term),
* `ERR`  the explicit expansion error of `Upsilon_expand` (`|Υval − Lval| ≤ ERR`),
* `NB := 45·Wval⁴/Δ`  the near-integer error of `Upsilon_near_int` (`distInt Υval ≤ NB`),

the §5 Step-4 extraction (writeup line 1042) is purely an *arithmetic rounding* statement:
take `s := round Υval`.  The three magnitude facts that drive it are the writeup's:

* `NB, ERR` are small (`< ½`) — they are `O(W⁴/Δ)` resp. `O(Δ⁴/H²·G⁵U⁴⁵/Ω¹⁴ + G⁴U²⁰/Δ)`;
* the leading term is **large**, `|Lval| ≥ 1 + ERR` — this is exactly the consequence of the
  large-defect threshold `|v| ≥ V₂` (`|p₁| ≫ |p₂|/d`, writeup 1029–1033), forcing `|Υval| ≥ 1`;
* the leading term is bounded, `|Lval| + ERR + 1 ≤ Bnd` with `Bnd = 10^k·G⁵U³⁵/Ω⁸` (writeup 1035).

This module isolates the rounding/extraction logic (the conceptual crux of Step 4) from the
scale arithmetic that produces those three magnitude inequalities.  The hypotheses `hexp`,
`hnear` are *exactly* the conclusions of `Upsilon_expand` / `Upsilon_near_int`, so the caller
discharges them by `exact`; the three magnitude inputs come from the §5 scale lemmas.
-/

namespace Squarefree

open Squarefree.Counting

set_option maxHeartbeats 800000

/-- **Rounding core.** If `Υval` is within `NB < ½` of an integer, within `ERR` of a value
`Lval` with `|Lval| ≥ 1 + ERR`, and `|Lval| + ERR + 1 ≤ Bnd`, then `s := round Υval` is a
**nonzero** integer with `|s| ≤ Bnd` and `|Υval − s| ≤ NB`. -/
theorem round_extract_core {Υval Lval ERR NB Bnd : ℝ}
    (hNB : NB < 1 / 2)
    (hexp : |Υval - Lval| ≤ ERR)
    (hnear : distInt Υval ≤ NB)
    (hLlo : 1 + ERR ≤ |Lval|)
    (hBnd : |Lval| + ERR + 1 ≤ Bnd) :
    ∃ s : ℤ, s ≠ 0 ∧ |(s : ℝ)| ≤ Bnd ∧ |Υval - (s : ℝ)| ≤ NB := by
  refine ⟨round Υval, ?_, ?_, ?_⟩
  · -- s ≠ 0 : |Υval| ≥ 1, and |Υval − round Υval| ≤ NB < ½, so |round Υval| ≥ ½ > 0.
    -- |Υval| ≥ |Lval| − |Υval − Lval| ≥ (1+ERR) − ERR = 1.
    have hΥabs : (1 : ℝ) ≤ |Υval| := by
      have h1 : |Lval| - |Υval - Lval| ≤ |Υval| := by
        have := abs_sub_abs_le_abs_sub Lval Υval
        rw [abs_sub_comm Lval Υval] at this
        linarith [this]
      linarith [hexp, hLlo]
    intro hzero
    -- with s = 0 : |Υval| = |Υval − round Υval| = distInt Υval ≤ NB < ½ < 1, contradiction.
    have hround0 : (round Υval : ℝ) = 0 := by rw [hzero]; simp
    have hd : distInt Υval = |Υval| := by
      simp only [distInt, hround0, sub_zero]
    rw [hd] at hnear
    linarith [hΥabs, hnear, hNB]
  · -- |round Υval| ≤ Bnd : |round Υval| ≤ |Υval| + NB ≤ (|Lval|+ERR) + NB ≤ Bnd.
    have hdle : |Υval - (round Υval : ℝ)| ≤ NB := hnear
    have htri : |(round Υval : ℝ)| ≤ |Υval| + |Υval - (round Υval : ℝ)| := by
      have h1 : |(round Υval : ℝ)| - |Υval| ≤ |(round Υval : ℝ) - Υval| :=
        abs_sub_abs_le_abs_sub _ _
      rw [abs_sub_comm (round Υval : ℝ) Υval] at h1
      linarith [h1]
    have hΥub : |Υval| ≤ |Lval| + ERR := by
      have h1 : |Υval| - |Lval| ≤ |Υval - Lval| := abs_sub_abs_le_abs_sub Υval Lval
      linarith [hexp]
    have hNB12 : NB ≤ 1 := by linarith [hNB]
    calc |(round Υval : ℝ)| ≤ |Υval| + |Υval - (round Υval : ℝ)| := htri
      _ ≤ (|Lval| + ERR) + NB := by linarith [hΥub, hdle]
      _ ≤ |Lval| + ERR + 1 := by linarith [hNB12]
      _ ≤ Bnd := hBnd
  · -- third conjunct: |Υval − round Υval| = distInt Υval ≤ NB.  Free.
    exact hnear

/-- **§5 Step-4 integer extraction** (writeup 1033–1043).  Public form, phrased in the §5
scales `Wval = G·U⁵`, `Δ`, `Ω`, `G`, `U`.  Under the large-defect range (encoded by the
leading-term lower bound `hLlo`, the writeup's consequence of `|v| ≥ V₂`), the near-integer
`Υval` rounds to a **nonzero** integer `s` with `1 ≤ |s| ≤ 10⁸⁰·G⁵U³⁵/Ω⁸` and `Υval` within
`45·Wval⁴/Δ` of `s`.  (The `10⁸⁰` is the writeup's absolute `≪`-constant made explicit; it
absorbs the large per-`r` magnitude inputs `|b₀| ≤ 3·10¹²B`, `|v| ≤ 10²⁰·ΔU⁵/Ω³`.)

The hypotheses `hexp` / `hnear` are *exactly* the conclusions of `Upsilon_expand` /
`Upsilon_near_int` (`hexp` says `Υval` is within the expansion error `ERR` of the leading
value `Lval`; `hnear` is the near-integer bound, here named `NB = 45·Wval⁴/Δ`); the caller
discharges them with those two lemmas.  The three magnitude inequalities (`hNBsmall`,
`hLlo`, `hLhi`) are the writeup's scale facts: the near-integer error is `< ¼` (`< ½`
suffices), the leading term is `≥ 1 + ERR` (the `V₂`-driven lower bound, writeup 1029–1033)
and bounded above by the `G⁵U³⁵/Ω⁸` budget (writeup 1035). -/
theorem Upsilon_s_extract {P : Globals} (S : Scale P) {Υval Lval ERR NB : ℝ}
    (hexp : |Υval - Lval| ≤ ERR)
    (hnear : NB = 10 ^ 11 * P.Wval ^ 4 / S.Δ)
    (hnearbd : distInt Υval ≤ NB)
    (hNBsmall : NB < 1 / 4)
    (hLlo : 1 + ERR ≤ |Lval|)
    (hLhi : |Lval| + ERR + 1 ≤ 10 ^ 120 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)) :
    ∃ s : ℤ, s ≠ 0
      ∧ |(s : ℝ)| ≤ 10 ^ 120 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8)
      ∧ |Υval - (s : ℝ)| ≤ 10 ^ 11 * P.Wval ^ 4 / S.Δ := by
  subst hnear
  have hNBhalf : 10 ^ 11 * P.Wval ^ 4 / S.Δ < 1 / 2 := by linarith [hNBsmall]
  obtain ⟨s, hs0, hsbd, hsnear⟩ :=
    round_extract_core (Υval := Υval) (Lval := Lval) (ERR := ERR)
      (NB := 10 ^ 11 * P.Wval ^ 4 / S.Δ)
      (Bnd := 10 ^ 120 * (P.G ^ 5 * P.U ^ 35 / S.Ω ^ 8))
      hNBhalf hexp hnearbd hLlo hLhi
  exact ⟨s, hs0, hsbd, hsnear⟩

end Squarefree
