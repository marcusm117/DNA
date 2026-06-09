import SystemE
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

namespace Elements.Book2

/-
Pure length-arithmetic core of Prop 2.11 (golden section).
Serves Book2/Prop11.lean's final equality.

All hypotheses are stated ADDITIVELY/multiplicatively (no subtraction, no `2*`
literal), because the System-E SMT translator only handles `+`, `*`, `/` and
Nat literals — so these are exactly the equalities `euclid_finish` can supply
from the construction.

Naming (segment lengths, all ≥ 0):
  A  = |ab|   (whole line)
  M  = |am| = |mb|   (the two halves from bisecting AB at m)
  E  = |ae|          (cut on the perpendicular, made equal to M)
  Q  = |eb|          (hypotenuse of right triangle a-e-b)
  F  = |af|          (= Q − E, via |ef| = |ae| + |af| and |ef| = |eb|)
  AH = |ah|          (the golden cut, made equal to F)
  BH = |bh|          (remaining piece)

Hypotheses (each matches one construction fact):
  hA  : A = M + M           -- |ab| = |am| + |mb|,  with |am| = |mb|
  hE  : E = M               -- |ae| = |am|
  hpy : Q*Q = E*E + A*A     -- Pythagoras on right triangle a-e-b (Prop 1.47)
  hQ  : Q = E + F           -- |eb| = |ae| + |af|  (between e a f, |ef| = |eb|)
  hAH : AH = F              -- |ah| = |af|
  hBH : A = AH + BH         -- |ab| = |ah| + |hb|  (between a h b)

Goal: A * BH = AH * AH   (i.e. |ab|·|bh| = |ah|·|ah|, the golden-section equality).

Algebra: substituting gives A = 2M, AH = F, Q = M + F; Pythagoras becomes
(M+F)² = 5M², i.e. F² = 4M² − 2MF; and the goal 2M·(2M−F) = F² is the same.
-/
theorem helper_11_golden (A M E Q F AH BH : ℝ)
    (hA : A = M + M) (hE : E = M) (hpy : Q * Q = E * E + A * A)
    (hQ : Q = E + F) (hAH : AH = F) (hBH : A = AH + BH) :
    A * BH = AH * AH := by
  -- `subst hE` eliminates M (keeping E); after the chain survivors are E, F, BH with
  --   hBH : E + E = F + BH,   hpy : (E+F)*(E+F) = E*E + (E+E)*(E+E),   goal : (E+E)*BH = F*F.
  subst hE hQ hA hAH
  linear_combination (-2 * E) * hBH - hpy

/-
Magnitude fact needed by the `proposition_3` cut (|af| < |ab|): the √5 length
|eb| = √5·|am| satisfies |af| = |eb| − |ae| = (√5−1)|am| < 2|am| = |ab|.
Stated with the same additive hypotheses; needs |am| > 0 (a,m,b distinct).
-/
theorem helper_11_af_lt_ab (A M E Q F : ℝ)
    (hM : M > 0) (hA : A = M + M) (hE : E = M)
    (hpy : Q * Q = E * E + A * A) (hQ : Q = E + F)
    (hQnn : Q ≥ 0) :
    F < A := by
  subst hE hA
  -- F = Q − M (hQ), A = 2M, Q² = 5M², Q ≥ 0, M > 0  ⟹  Q < 3M  ⟹  F < 2M = A
  nlinarith [hpy, hQnn, hM, hQ]

end Elements.Book2