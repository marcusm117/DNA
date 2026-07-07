import SystemE
import Book.Prop19
import Book3.Prop02.step9_inside
import Book3.Prop02.step9_tri
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_2_step9 (a b d p : Point) (ABC : Circle) (DB DFE : Line)
    (ha : a.onCircle ABC) (hb : b.onCircle ABC) (hd : d.isCentre ABC)
    (hdDFE : d.onLine DFE) (hpDFE : p.onLine DFE)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (hdb_ne : d ≠ b)
    (hbet : between a p b)
    (hnotinside : ¬p.insideCircle ABC)
    (hassump1 : ∠ d:p:b > ∠ d:b:p) :
    |(d─b)| > |(d─p)| := by
  euclid_apply (line_from_points p b) as PB
  by_cases hd_PB : d.onLine PB
  · -- @args: a b p ABC
    have step9_inside : p.insideCircle ABC := by euclid_apply (helper_3_2_step9_inside a b p ABC (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show between a p b; assumption)))
    exact absurd step9_inside hnotinside
  ·
    have hdp_ne : d ≠ p := by euclid_finish
    have hpb_ne : p ≠ b := by euclid_finish
    -- @args: d p b DFE PB DB
    have step9_tri : formTriangle d p b DFE PB DB := by euclid_apply (helper_3_2_step9_tri d p b DFE PB DB (by euclid_assumption "" (show d.onLine DFE; assumption)) (by euclid_assumption "" (show p.onLine DFE; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show p.onLine PB; assumption)) (by euclid_assumption "" (show b.onLine PB; assumption)) (by euclid_assumption "" (show d ≠ p; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show p ≠ b; assumption)) (by euclid_assumption "" (show ¬d.onLine PB; assumption)))
    euclid_apply (proposition_19 d p b DFE PB DB)
    euclid_finish

end Elements.Book3
