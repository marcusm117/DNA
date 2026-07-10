import SystemE
import Mathlib.Tactic.Linarith
import Book3.Prop08.step5_assumption1
import Book3.Prop08.step5_p20
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Binders include everything step5_assumption1 needs for SP, plus the original goal hyps.
theorem helper_3_8_step5
    (ABC : Circle) (m e f d g a : Point) (ME AG : Line)
    (hm : m.isCentre ABC) (he : e.onCircle ABC) (ha : a.onCircle ABC) (hg : g.onCircle ABC)
    (hdnot : ¬d.onCircle ABC)
    (hdAG : d.onLine AG) (haAG : a.onLine AG) (hgAG : g.onLine AG)
    (hbetdgm : between d g m) (hbetgma : between g m a)
    (hne_ea : e ≠ a)
    (hang : ∠e:m:d > ∠f:m:d)
    (hMEm : m.onLine ME) (hMEe : e.onLine ME)
    (hstep4 : |(d─a)| = |(e─m)| + |(m─d)|)
    (hassump1 : |(e─m)| + |(m─d)| > |(e─d)|) :
    |(d─a)| > |(d─e)| := by
  -- Re-cite step5_assumption1 as a cone sub-node so its proposition_20 call satisfies criterion-3.
  have step5_assumption1 : |(e─m)| + |(m─d)| > |(e─d)| := by euclid_apply (helper_3_8_step5_assumption1 ABC m e f d g a ME AG (by euclid_assumption "" (show m.isCentre ABC; assumption)) (by euclid_assumption "" (show e.onCircle ABC; assumption)) (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show g.onCircle ABC; assumption)) (by euclid_assumption "" (show ¬d.onCircle ABC; assumption)) (by euclid_assumption "" (show d.onLine AG; assumption)) (by euclid_assumption "" (show a.onLine AG; assumption)) (by euclid_assumption "" (show g.onLine AG; assumption)) (by euclid_assumption "" (show between d g m; assumption)) (by euclid_assumption "" (show between g m a; assumption)) (by euclid_assumption "" (show e ≠ a; assumption)) (by euclid_assumption "" (show ∠ e:m:d > ∠ f:m:d; assumption)) (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)))
  have step5_p20 : |(e─m)| + |(m─d)| > |(e─d)| := by euclid_apply (helper_3_8_step5_p20 m e d (by euclid_assumption "" (show |(e─m)| + |(m─d)| > |(e─d)|; assumption)))
  euclid_finish

end Elements.Book3
