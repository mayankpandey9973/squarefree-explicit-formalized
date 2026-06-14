import Squarefree.Lower.Step2Phi3
import Squarefree.Lower.Step2ChiPos
import Squarefree.Lower.DefectBt3

/-!
# §5 Step-2 φ″-zero count — algebraic core (the `f`-free Wronskian `W₂`)

The §5 Step-2 φ″-zero count differentiates the ratio `m = −χ″/ψ″` (`χ = ψ·φ`, `ψ = d̃⁴/(6Xa)`):
since `φ_f″ = f·ψ″ + χ″` and `ψ″ > 0`, the zero set `{r : φ_f″(r) = 0}` is the graph `f = m(r)`,
so the per-band zero count is `≤ 1` once `m` is strictly monotone.  By the quotient rule

  `d/dr(χ″/ψ″) = (χ‴ψ″ − χ″ψ‴)/(ψ″)² = W₂/(ψ″)²`,  `W₂ := χ‴ψ″ − χ″ψ‴`,

so the sign of `m' = −W₂/(ψ″)²` is fixed by the sign of the `f`-free Wronskian `W₂`.

This module supplies the **symbolic Wronskian identity** `welim2_poly` (order-2 analogue of
`welim_poly`): expanding `χ″ = ψ″φ + 2ψ'φ' + ψφ''` and `χ‴ = ψ‴φ + 3ψ″φ' + 3ψ'φ'' + ψφ'''`
(the `phif_iteratedDeriv{2,3}_eq` forms at `f = 0`), the `φ`-coefficient `(ψ‴ψ″ − ψ″ψ‴)φ` cancels
and `W₂` collapses to

  `W₂ = (3ψ″² − 2ψ'ψ‴)·φ' + (3ψ'ψ″ − ψψ‴)·φ'' + ψψ″·φ'''`.

**Smooth value (sympy-verified, sign-definite).**  Replacing the finite-difference atoms by their
smooth limits (`b̃→d̃'`, …, `b̃‴→d̃⁗`) and substituting the `d̃`-tower closed forms gives the
all-positive-numerator closed form

  `W₂_smooth = −3·d̃⁵·(a+d̃)³·P₈(a,d̃) / (16·r⁷·(a+2d̃)¹¹·(6Xa)²) < 0`,

  `P₈ = 35a⁸ + 552a⁷d̃ + 4014a⁶d̃² + 16847a⁵d̃³ + 44170a⁴d̃⁴ + 74048a³d̃⁵ + 77708a²d̃⁶`
       `+ 46840a d̃⁷ + 12480 d̃⁸ > 0`,

equivalently `d/dr(χ_s″/ψ″) = W₂_smooth/(ψ″)² = −3(a+d̃)·P₈ /
(16r³(a+2d̃)⁵(6a²+19ad̃+16d̃²)²d̃³) < 0`.  (The `(6a²+19ad̃+16d̃²)²` of the ratio-derivative
denominator is exactly `(ψ″·6Xa·r²(a+2d̃)³/(d̃⁴(a+d̃)))²`, which cancels against `(ψ″)²`.)
-/

namespace Squarefree

open Real

set_option maxHeartbeats 1600000

/-- **The `f`-free Wronskian identity `W₂ = χ‴ψ″ − χ″ψ‴`** (order-2 analogue of `welim_poly`).
With the `phif_iteratedDeriv{2,3}_eq` atom expansions at `f = 0`
(`χ″ = ψ″φ + 2ψ'φ' + ψφ''`, `χ‴ = ψ‴φ + 3ψ″φ' + 3ψ'φ'' + ψφ'''`, ψ-tower in `d̃`-atoms), the
`φ`-coefficient cancels and `W₂` equals `(3ψ″²−2ψ'ψ‴)φ' + (3ψ'ψ″−ψψ‴)φ'' + ψψ″φ'''`, keeping the
`φ`-tower `φ',φ'',φ'''` symbolic (exactly as `phif_iteratedDeriv3_eq` keeps `φ'''` symbolic). -/
lemma welim2_poly (X a d d1 d2 s4 φ φ1 φ2 φ3 : ℝ) (_hg : (6 : ℝ) * X * a ≠ 0) :
    ((24 * d * d1 ^ 3 + 36 * d ^ 2 * d1 * d2 + 4 * d ^ 3 * s4) / (6 * X * a) * φ
          + (36 * d ^ 2 * d1 ^ 2 + 12 * d ^ 3 * d2) / (6 * X * a) * φ1
          + (12 * d ^ 3 * d1) / (6 * X * a) * φ2
          + d ^ 4 / (6 * X * a) * φ3)
        * ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a))
      - ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a) * φ
          + (8 * d ^ 3 * d1) / (6 * X * a) * φ1
          + d ^ 4 / (6 * X * a) * φ2)
        * ((24 * d * d1 ^ 3 + 36 * d ^ 2 * d1 * d2 + 4 * d ^ 3 * s4) / (6 * X * a))
      = (3 * ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a)) ^ 2
            - 2 * (4 * d ^ 3 * d1 / (6 * X * a))
                * ((24 * d * d1 ^ 3 + 36 * d ^ 2 * d1 * d2 + 4 * d ^ 3 * s4) / (6 * X * a))) * φ1
        + (3 * (4 * d ^ 3 * d1 / (6 * X * a))
              * ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a))
            - (d ^ 4 / (6 * X * a))
                * ((24 * d * d1 ^ 3 + 36 * d ^ 2 * d1 * d2 + 4 * d ^ 3 * s4) / (6 * X * a))) * φ2
        + (d ^ 4 / (6 * X * a))
            * ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a)) * φ3 := by
  field_simp
  ring

/-- **The `f`-free Wronskian as a single cleared fraction `W₂ = (K/(6Xa)²)·W2num/d²`** (order-2
analogue of `chi2_poly`).  Substituting the closed `φ`-tower forms `φ' = K b(2 b' d − 5 b d̃')/d⁶`,
`φ''`, `φ''' = K·Q/d⁸` (b-tower symbolic) into the `welim2_poly` right-hand side collapses to the
17-monomial numerator
`W2num = −20 b² d² d̃'² s4 + 60 b² d² d̃' d̃''² − 120 b² d̃'⁵ − 8 b b'' d⁴ s4 − 96 b b'' d³ d̃' d̃''`
`− 120 b b'' d² d̃'³ + 16 b b' d³ d̃' s4 − 24 b b' d³ d̃''² + 120 b b' d² d̃'² d̃'' + 240 b b' d d̃'⁴`
`+ 8 b b''' d⁴ d̃'' + 24 b b''' d³ d̃'² + 24 b'' b' d⁴ d̃'' + 72 b'' b' d³ d̃'² − 8 b'² d⁴ s4`
`− 96 b'² d³ d̃' d̃'' − 120 b'² d² d̃'³` (sympy-verified). -/
lemma w2_poly (X a d d1 d2 s4 b bp bd bt3 K : ℝ) (hd : d ≠ 0) (h6 : (6 : ℝ) * X * a ≠ 0) :
    (3 * ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a)) ^ 2
          - 2 * (4 * d ^ 3 * d1 / (6 * X * a))
              * ((24 * d * d1 ^ 3 + 36 * d ^ 2 * d1 * d2 + 4 * d ^ 3 * s4) / (6 * X * a)))
        * (K * b * (2 * bp * d - 5 * b * d1) / d ^ 6)
      + (3 * (4 * d ^ 3 * d1 / (6 * X * a))
              * ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a))
            - (d ^ 4 / (6 * X * a))
                * ((24 * d * d1 ^ 3 + 36 * d ^ 2 * d1 * d2 + 4 * d ^ 3 * s4) / (6 * X * a)))
        * (K * (bp * (2 * bp * d - 5 * b * d1) + b * (2 * bd * d - 3 * bp * d1 - 5 * b * d2)
              - 6 * b * (2 * bp * d - 5 * b * d1) * d1 / d) / d ^ 6)
      + (d ^ 4 / (6 * X * a)) * ((12 * d ^ 2 * d1 ^ 2 + 4 * d ^ 3 * d2) / (6 * X * a))
        * (K * (6 * d ^ 3 * bp * bd + 2 * d ^ 3 * b * bt3 + 180 * d * d1 ^ 2 * b * bp
              + 90 * d * d1 * d2 * b ^ 2 - 30 * d ^ 2 * d1 * bp ^ 2 - 30 * d ^ 2 * d1 * b * bd
              - 30 * d ^ 2 * d2 * b * bp - 5 * d ^ 2 * s4 * b ^ 2 - 210 * d1 ^ 3 * b ^ 2) / d ^ 8)
      = K / (6 * X * a) ^ 2
          * (-20 * b ^ 2 * d ^ 2 * d1 ^ 2 * s4 + 60 * b ^ 2 * d ^ 2 * d1 * d2 ^ 2
              - 120 * b ^ 2 * d1 ^ 5 - 8 * b * bd * d ^ 4 * s4 - 96 * b * bd * d ^ 3 * d1 * d2
              - 120 * b * bd * d ^ 2 * d1 ^ 3 + 16 * b * bp * d ^ 3 * d1 * s4
              - 24 * b * bp * d ^ 3 * d2 ^ 2 + 120 * b * bp * d ^ 2 * d1 ^ 2 * d2
              + 240 * b * bp * d * d1 ^ 4 + 8 * b * bt3 * d ^ 4 * d2 + 24 * b * bt3 * d ^ 3 * d1 ^ 2
              + 24 * bd * bp * d ^ 4 * d2 + 72 * bd * bp * d ^ 3 * d1 ^ 2 - 8 * bp ^ 2 * d ^ 4 * s4
              - 96 * bp ^ 2 * d ^ 3 * d1 * d2 - 120 * bp ^ 2 * d ^ 2 * d1 ^ 3) / d ^ 2 := by
  field_simp
  ring

/-- **Smooth `W₂` numerator closed form** (sympy-verified, sign-definite `< 0`).  With the smooth
substitution `b → d̃', b' → d̃'', b'' → d̃''', b''' → d̃''''` the 17-monomial `W2num` collapses to the
10-monomial smooth numerator `W2num_s = 8 d⁴ d̃' d̃'' d̃'''' − 8 d⁴ d̃' d̃'''² + 16 d⁴ d̃''² d̃''' + ...`,
and substituting the `d̃`-tower closed forms gives
`W2num_s = −3 d̃⁷ (a+d̃)³ P₈ / (16 r⁷ (a+2d̃)¹¹)` with
`P₈ = 35a⁸+552a⁷d̃+4014a⁶d̃²+16847a⁵d̃³+44170a⁴d̃⁴+74048a³d̃⁵+77708a²d̃⁶+46840a d̃⁷+12480 d̃⁸ > 0`. -/
lemma smooth_W2_eq (a d r : ℝ) (hr : r ≠ 0) (had2 : a + 2 * d ≠ 0) :
    8 * d ^ 4 * (-d * (d + a) / (2 * r * (a + 2 * d)))
          * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) / (4 * r ^ 2 * (a + 2 * d) ^ 3))
          * (3 * d * (d + a)
              * (35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
                  + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6)
              / (16 * r ^ 4 * (a + 2 * d) ^ 7))
        - 8 * d ^ 4 * (-d * (d + a) / (2 * r * (a + 2 * d)))
          * (-3 * d * (d + a)
              * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4)
              / (8 * r ^ 3 * (a + 2 * d) ^ 5)) ^ 2
        + 16 * d ^ 4
          * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) / (4 * r ^ 2 * (a + 2 * d) ^ 3)) ^ 2
          * (-3 * d * (d + a)
              * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4)
              / (8 * r ^ 3 * (a + 2 * d) ^ 5))
        + 24 * d ^ 3 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 3
          * (3 * d * (d + a)
              * (35 * a ^ 6 + 362 * a ^ 5 * d + 1650 * a ^ 4 * d ^ 2 + 4136 * a ^ 3 * d ^ 3
                  + 5968 * a ^ 2 * d ^ 4 + 4680 * a * d ^ 5 + 1560 * d ^ 6)
              / (16 * r ^ 4 * (a + 2 * d) ^ 7))
        - 8 * d ^ 3 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 2
          * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) / (4 * r ^ 2 * (a + 2 * d) ^ 3))
          * (-3 * d * (d + a)
              * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4)
              / (8 * r ^ 3 * (a + 2 * d) ^ 5))
        - 120 * d ^ 3 * (-d * (d + a) / (2 * r * (a + 2 * d)))
          * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) / (4 * r ^ 2 * (a + 2 * d) ^ 3)) ^ 3
        - 140 * d ^ 2 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 4
          * (-3 * d * (d + a)
              * (5 * a ^ 4 + 34 * a ^ 3 * d + 94 * a ^ 2 * d ^ 2 + 120 * a * d ^ 3 + 60 * d ^ 4)
              / (8 * r ^ 3 * (a + 2 * d) ^ 5))
        + 60 * d ^ 2 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 3
          * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) / (4 * r ^ 2 * (a + 2 * d) ^ 3)) ^ 2
        + 240 * d * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 5
          * (d * (d + a) * (3 * a ^ 2 + 10 * a * d + 10 * d ^ 2) / (4 * r ^ 2 * (a + 2 * d) ^ 3))
        - 120 * (-d * (d + a) / (2 * r * (a + 2 * d))) ^ 7
      = -3 * d ^ 7 * (a + d) ^ 3
          * (35 * a ^ 8 + 552 * a ^ 7 * d + 4014 * a ^ 6 * d ^ 2 + 16847 * a ^ 5 * d ^ 3
              + 44170 * a ^ 4 * d ^ 4 + 74048 * a ^ 3 * d ^ 5 + 77708 * a ^ 2 * d ^ 6
              + 46840 * a * d ^ 7 + 12480 * d ^ 8)
        / (16 * r ^ 7 * (a + 2 * d) ^ 11) := by
  field_simp
  ring

/-- **Finite-difference correction expansion for `W2num`** (sympy-verified, 37 groups).  Writing the
actual `b`-tower as `b = d̃'+ε₁, b' = d̃''+ε₂, b'' = d̃'''+ε₃, b''' = d̃''''+ε₄` and subtracting the
smooth numerator `W2num_s` gives a 37-monomial polynomial, each carrying at least one `εᵢ`. -/
lemma Ncorr_w2_alg (d d1 d2 s4 d4 e1 e2 e3 e4 : ℝ) :
    (-20 * (d1 + e1) ^ 2 * d ^ 2 * d1 ^ 2 * s4 + 60 * (d1 + e1) ^ 2 * d ^ 2 * d1 * d2 ^ 2
        - 120 * (d1 + e1) ^ 2 * d1 ^ 5 - 8 * (d1 + e1) * (s4 + e3) * d ^ 4 * s4
        - 96 * (d1 + e1) * (s4 + e3) * d ^ 3 * d1 * d2 - 120 * (d1 + e1) * (s4 + e3) * d ^ 2 * d1 ^ 3
        + 16 * (d1 + e1) * (d2 + e2) * d ^ 3 * d1 * s4 - 24 * (d1 + e1) * (d2 + e2) * d ^ 3 * d2 ^ 2
        + 120 * (d1 + e1) * (d2 + e2) * d ^ 2 * d1 ^ 2 * d2
        + 240 * (d1 + e1) * (d2 + e2) * d * d1 ^ 4 + 8 * (d1 + e1) * (d4 + e4) * d ^ 4 * d2
        + 24 * (d1 + e1) * (d4 + e4) * d ^ 3 * d1 ^ 2 + 24 * (s4 + e3) * (d2 + e2) * d ^ 4 * d2
        + 72 * (s4 + e3) * (d2 + e2) * d ^ 3 * d1 ^ 2 - 8 * (d2 + e2) ^ 2 * d ^ 4 * s4
        - 96 * (d2 + e2) ^ 2 * d ^ 3 * d1 * d2 - 120 * (d2 + e2) ^ 2 * d ^ 2 * d1 ^ 3)
      - (8 * d ^ 4 * d1 * d2 * d4 - 8 * d ^ 4 * d1 * s4 ^ 2 + 16 * d ^ 4 * d2 ^ 2 * s4
          + 24 * d ^ 3 * d1 ^ 3 * d4 - 8 * d ^ 3 * d1 ^ 2 * d2 * s4 - 120 * d ^ 3 * d1 * d2 ^ 3
          - 140 * d ^ 2 * d1 ^ 4 * s4 + 60 * d ^ 2 * d1 ^ 3 * d2 ^ 2 + 240 * d * d1 ^ 5 * d2
          - 120 * d1 ^ 7)
      = 8 * d ^ 4 * d1 * d2 * e4 - 8 * d ^ 4 * d1 * e3 * s4 + 24 * d ^ 4 * d2 ^ 2 * e3
        + 8 * d ^ 4 * d2 * d4 * e1 + 8 * d ^ 4 * d2 * e1 * e4 + 24 * d ^ 4 * d2 * e2 * e3
        + 8 * d ^ 4 * d2 * e2 * s4 - 8 * d ^ 4 * e1 * e3 * s4 - 8 * d ^ 4 * e1 * s4 ^ 2
        - 8 * d ^ 4 * e2 ^ 2 * s4 + 24 * d ^ 3 * d1 ^ 3 * e4 - 24 * d ^ 3 * d1 ^ 2 * d2 * e3
        + 24 * d ^ 3 * d1 ^ 2 * d4 * e1 + 24 * d ^ 3 * d1 ^ 2 * e1 * e4 + 72 * d ^ 3 * d1 ^ 2 * e2 * e3
        + 88 * d ^ 3 * d1 ^ 2 * e2 * s4 - 216 * d ^ 3 * d1 * d2 ^ 2 * e2 - 96 * d ^ 3 * d1 * d2 * e1 * e3
        - 80 * d ^ 3 * d1 * d2 * e1 * s4 - 96 * d ^ 3 * d1 * d2 * e2 ^ 2 + 16 * d ^ 3 * d1 * e1 * e2 * s4
        - 24 * d ^ 3 * d2 ^ 3 * e1 - 24 * d ^ 3 * d2 ^ 2 * e1 * e2 - 120 * d ^ 2 * d1 ^ 4 * e3
        - 120 * d ^ 2 * d1 ^ 3 * d2 * e2 - 120 * d ^ 2 * d1 ^ 3 * e1 * e3 - 160 * d ^ 2 * d1 ^ 3 * e1 * s4
        - 120 * d ^ 2 * d1 ^ 3 * e2 ^ 2 + 240 * d ^ 2 * d1 ^ 2 * d2 ^ 2 * e1
        + 120 * d ^ 2 * d1 ^ 2 * d2 * e1 * e2 - 20 * d ^ 2 * d1 ^ 2 * e1 ^ 2 * s4
        + 60 * d ^ 2 * d1 * d2 ^ 2 * e1 ^ 2 + 240 * d * d1 ^ 5 * e2 + 240 * d * d1 ^ 4 * d2 * e1
        + 240 * d * d1 ^ 4 * e1 * e2 - 240 * d1 ^ 6 * e1 - 120 * d1 ^ 5 * e1 ^ 2 := by
  ring

end Squarefree
