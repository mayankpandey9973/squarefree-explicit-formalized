import Squarefree.Lower.Step4Cref
import Squarefree.Lower.DefectBounds
import Squarefree.Lower.Step2CurvCurv2

/-!
# §5 Step-4 discrete-vs-smooth slope reconciliation (`hb0gap`, writeup 690–702)

The large-defect witness discrete slope

  `b₀ = (d_a^*(r+ℓ₁) − d_a^*(r))/ℓ₁`

is reconciled with the **smooth-slope model** `b1Model P.X a (d̃ₐ(r))`, which — via the
`R_a` relation `r = X a³/(d²(d+a)²)` at the smooth point `d = d̃ₐ(r)` — is *exactly* the
defect-inverse derivative `d̃ₐ'(r)` (`b1Model_eq_dtilde_deriv`).  This is the value the §5
Step-4 flatness machinery (`Cprime_b1Model_eq`, `Step4Cref`) substitutes for `b₀`, and the
form the diameter assembly (`Sigma_closed_diff_Cref_le`, `Step4Diam`) consumes as its
`hb0gap` hypothesis (the fibre-extract `Σ_closed` is evaluated at the smooth point `d̃ₐ(r)`).

The gap splits into two pieces (writeup 690–702, 718–723):

* **(i) the `d_a^*`-vs-`d̃ₐ` defect (Prop 3.2).**  Replacing `d_a^*` by `d̃ₐ` at both `r` and
  `r+ℓ₁` costs `2·10¹²·(Δ/(GΩ³))/ℓ₁`, the writeup's `O(Δ/(ℓ₁GΩ³))`.
* **(ii) finite-difference vs derivative.**  The smooth quotient
  `(d̃ₐ(r+ℓ₁) − d̃ₐ(r))/ℓ₁` differs from `d̃ₐ'(r)` by at most `ℓ₁·sup_{[r,r+ℓ₁]}|d̃ₐ''|`,
  bounded (via the double MVT `fd_error_bound` and `dtilde_d2_bounds`) by
  `ℓ₁·10¹³·(B/R)`.

So `gap = 2·10¹²·(Δ/(GΩ³))/ℓ₁ + ℓ₁·10¹³·(B/R)`, with the (i) term carrying the dominant
`Δ/(ℓ₁GΩ³)` scale.  The downstream size collapse bounds each piece against the `E_recon`
budget.
-/

namespace Squarefree

open Real

variable {P : Globals} {S : Scale P}

/-- **The smooth-slope model is exactly `d̃ₐ'(r)`** (the `R_a`-relation identity).  At the smooth
point `d = d̃ₐ(r)`, the relation `r = X a³/(d²(d+a)²)` (`dtilde_spec` + `Rfun_factor'`) turns the
flat reference slope `b1Model X a d = −d³(d+a)³/(2Xa³(2d+a))` into `−d(d+a)/(2r(a+2d))`, which is
the closed `r`-derivative of `d̃ₐ` (`dtilde_r_hasDerivAt`). -/
private theorem b1Model_eq_dtilde_deriv {X a r : ℝ} (hX : 0 < X) (ha : 0 < a) (hr : 0 < r) :
    b1Model X a (dtilde X r a) = deriv (fun s => dtilde X s a) r := by
  set d := dtilde X r a with hd_def
  have hd : 0 < d := dtilde_pos hX ha hr
  have hda : 0 < d + a := by linarith
  have h2da : 0 < 2 * d + a := by linarith
  -- the `R_a` relation, cleared of denominators
  have hXa3 : X * a ^ 3 = r * (d ^ 2 * (d + a) ^ 2) := by
    have hspec : Rfun X a d = r := dtilde_spec hX ha hr
    rw [Rfun_factor' X a d (ne_of_gt hd) (ne_of_gt hda)] at hspec
    rwa [div_eq_iff (by positivity : (d ^ 2 * (d + a) ^ 2) ≠ 0)] at hspec
  rw [(dtilde_r_hasDerivAt hX ha hr).deriv, ← hd_def]
  unfold b1Model
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (2 * d * (d + a) * (2 * d + a)) * hXa3

/-- **§5 Step-4 discrete-vs-smooth slope reconciliation** (writeup 702).  For a large-defect window
around `r` (`a ≍ A`, `r ≍ R`, `0 < ℓ₁`), with `D`-scale witnesses `d ≈ d̃ₐ(r)`, `dℓ ≈ d̃ₐ(r+ℓ₁)`
close to the smooth points (Prop 3.2 tolerance `10¹²·Δ/(GΩ³)`), the discrete slope
`b₀ = (dℓ − d)/ℓ₁` is close to the smooth-slope model `b1Model P.X a (d̃ₐ(r)) = d̃ₐ'(r)`:

  `|b₀ − b1Model P.X a (d̃ₐ(r))| ≤ 2·10¹²·(Δ/(GΩ³))/ℓ₁ + ℓ₁·10¹³·(B/R)`,

the dominant `O(Δ/(ℓ₁GΩ³))` term being the `d_a^*`-vs-`d̃ₐ` defect and the second the
finite-difference-vs-derivative error. -/
theorem step4_hb0gap {a r ℓ₁ d dℓ : ℝ}
    (hAD : 10 * S.A ≤ S.D) (ha0 : 0 < a)
    (ha_lo : S.A / 5 ≤ a) (ha_hi : a ≤ 11 * S.A)
    (hℓpos : 0 < ℓ₁)
    (hr_lo : (1 / 72) * S.R ≤ r) (hrl_hi : r + ℓ₁ ≤ 16 * S.R)
    (hd_close : |d - dtilde P.X r a| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)))
    (hdℓ_close : |dℓ - dtilde P.X (r + ℓ₁) a| ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))) :
    |(dℓ - d) / ℓ₁ - b1Model P.X a (dtilde P.X r a)|
      ≤ 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) / ℓ₁
        + ℓ₁ * (10000000000000 * (S.B / S.R)) := by
  have hRpos : 0 < S.R := by
    unfold Scale.R
    have := P.H_pos; have := P.G_pos; have := S.Ω_pos; have := S.Δ_pos; positivity
  have hr0 : 0 < r := lt_of_lt_of_le (mul_pos (by norm_num) hRpos) hr_lo
  rw [b1Model_eq_dtilde_deriv P.X_pos ha0 hr0]
  -- sup bound on `|d̃ₐ''|` over the window `[r, r+ℓ₁]`
  have hd2sup : ∀ x ∈ Set.Icc r (r + ℓ₁),
      |iteratedDeriv 2 (fun s => dtilde P.X s a) x| ≤ 10000000000000 * (S.B / S.R) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hr0 hx.1
    have hxl : (1 / 72) * S.R ≤ x := le_trans hr_lo hx.1
    have hxr : x ≤ 16 * S.R := le_trans hx.2 hrl_hi
    obtain ⟨hpos, _, hhi⟩ := dtilde_d2_bounds hAD ha0 hxpos ha_lo ha_hi hxl hxr
    rw [abs_of_pos hpos]; exact hhi
  -- (ii) finite-difference vs derivative, via the double mean-value bound
  have hfd : |(dtilde P.X (r + ℓ₁) a - dtilde P.X r a) / ℓ₁
        - deriv (fun s => dtilde P.X s a) r|
      ≤ ℓ₁ * (10000000000000 * (S.B / S.R)) := by
    have key := fd_error_bound (f := fun t => dtilde P.X t a)
      (g := fun t => deriv (fun s => dtilde P.X s a) t)
      (h := fun t => iteratedDeriv 2 (fun s => dtilde P.X s a) t)
      (M := 10000000000000 * (S.B / S.R)) hℓpos
      (fun x hx => by
        have hxpos : 0 < x := lt_of_lt_of_le hr0 hx.1
        have h := dtilde_r_hasDerivAt P.X_pos ha0 hxpos
        simpa only [h.deriv] using h)
      (fun x hx => by
        have hxpos : 0 < x := lt_of_lt_of_le hr0 hx.1
        exact dtilde_deriv_hasDerivAt P.X_pos ha0 hxpos)
      hd2sup
    simpa using key
  -- triangle through the smooth finite difference
  refine le_trans
    (abs_sub_le _ ((dtilde P.X (r + ℓ₁) a - dtilde P.X r a) / ℓ₁) _)
    (add_le_add ?_ hfd)
  -- (i) the `d_a^*`-vs-`d̃ₐ` defect
  rw [div_sub_div_same,
    show (dℓ - d) - (dtilde P.X (r + ℓ₁) a - dtilde P.X r a)
        = (dℓ - dtilde P.X (r + ℓ₁) a) - (d - dtilde P.X r a) by ring,
    abs_div, abs_of_pos hℓpos]
  gcongr
  calc |(dℓ - dtilde P.X (r + ℓ₁) a) - (d - dtilde P.X r a)|
      ≤ |dℓ - dtilde P.X (r + ℓ₁) a| + |d - dtilde P.X r a| := abs_sub _ _
    _ ≤ 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3))
          + 1000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := add_le_add hdℓ_close hd_close
    _ = 2000000000000 * (S.Δ / (P.G * S.Ω ^ 3)) := by ring

end Squarefree
