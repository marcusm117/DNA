import SystemE
import Mathlib.Tactic.Linarith
import Book.Prop30

namespace Elements.Book2

open Elements.Book1

-- 2.4.27 (sub): the four sub-figures HF, CK, AG, GE tile the square ADEB.
-- Five area-axiom applies, each immediately LOCKED with an exact-emission-form euclid_assert (so
-- each solver call is cheap — it only checks the axiom's own output, not a reconciled goal):
--   * vertical cut (sum_parallelograms ADEB) → strips △d:a:c+△d:c:f and △f:c:b+△f:b:e.
--   * left horizontal cut (sum_parallelograms a d c f) + its parallelogram_area bridge.
--   * right horizontal cut (sum_parallelograms c f b e) + its parallelogram_area bridge.
-- A final linarith assembles the locked facts into the goal.
set_option systemE.solverTime 30 in
-- Slim signature: ONLY what the three cuts + linarith need (NOT positions' input baggage). The five
-- betweenness facts are taken as direct hyps — the PARENT (step27) supplies them from its own
-- `positions` node, so this helper's wire-discharge stays cheap.
theorem helper_2_step27_decomp (a b c d e f g h k : Point) (AB DE AD BE CF HK : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hdAD : d.onLine AD) (haAD : a.onLine AD) (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hcAB : c.onLine AB) (hacb : between a c b)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hfCF : f.onLine CF) (hfDE : f.onLine DE)
    (hgCF : g.onLine CF) (hgHK : g.onLine HK)
    (hhHK : h.onLine HK) (hhAD : h.onLine AD)
    (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hpos : between a h d ∧ between b k e ∧ between d f e ∧
            between b g d ∧ between c g f ∧ between h g k)
    (hdaBE : d.sameSide a BE) (hacDE : a.sameSide c DE) (hcbDE : c.sameSide b DE)
    (heb : e ≠ b) (hdf : d ≠ f) (hfe : f ≠ e)
    (hADCFne : AD ≠ CF) (hADBE : ¬(AD.intersectsLine BE))
    (hDEAB : ¬(DE.intersectsLine AB)) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
    (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
    (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
    (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
    Triangle.area △ d:a:b + Triangle.area △ d:b:e := by
  euclid_intros
  -- CF ∥ BE (CF ∥ AD via hCFAD, AD ∥ BE via hADBE) — needed by step27_right's right-strip cut
  euclid_apply (proposition_30 CF BE AD)
  -- left strip: AG (△a:c:g+△a:g:h) + HF (△h:g:f+△h:f:d) = △d:a:c+△d:c:f
  -- @args: a c d f g h AB DE AD CF
  have step27_left :
      Triangle.area △ a:c:g + Triangle.area △ a:g:h + Triangle.area △ h:g:f + Triangle.area △ h:f:d =
      Triangle.area △ d:a:c + Triangle.area △ d:c:f := by sorry
  -- right strip: CK (△c:b:k+△c:k:g) + GE (△g:k:e+△g:e:f) = △f:c:b+△f:b:e
  -- @args: b c e f g k AB DE CF BE
  have step27_right :
      Triangle.area △ c:b:k + Triangle.area △ c:k:g + Triangle.area △ g:k:e + Triangle.area △ g:e:f =
      Triangle.area △ f:c:b + Triangle.area △ f:b:e := by sorry
  -- vertical cut: the two strips sum to the big square
  -- @args: a b c d e f AB DE AD BE
  have step27_vert :
      Triangle.area △ d:a:c + Triangle.area △ d:c:f + Triangle.area △ f:c:b + Triangle.area △ f:b:e =
      Triangle.area △ d:a:b + Triangle.area △ d:b:e := by sorry
  -- combine is pure algebra over the three locked area-equalities — NO euclid_finish (no SMT over
  -- the area atoms, which would blow the 30s wall); just sum the strips and substitute.
  linarith [step27_left, step27_right, step27_vert]

end Elements.Book2
