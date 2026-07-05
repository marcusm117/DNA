import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_28_step2 (a b d e f g h : Point) (EF : Line)
    (heonEF : e.onLine EF) (hfonEF : f.onLine EF)
    (hbet_ab : between a g b)
    (hbet_eh : between e g h)
    (hbet_ghf : between g h f)
    (hsameside : b.sameSide d EF) :
    a.opposingSides d EF := by
  have hgf : between e g f := between_trans_out e g h f ⟨hbet_eh, hbet_ghf⟩
  have hgonEF : g.onLine EF := between_same_line_in e g f EF ⟨hgf, heonEF, hfonEF⟩
  have hnbonEF : ¬b.onLine EF := same_side_not_on_line b d EF hsameside
  have hdsidesymm := same_side_symm b d EF hsameside
  have hndonEF : ¬d.onLine EF := same_side_not_on_line d b EF hdsidesymm
  have hnsab : ¬(a.sameSide b EF) := pasch_3 a g b EF ⟨hbet_ab, hgonEF⟩
  have hnaonEF : ¬a.onLine EF := by
    intro haonEF
    exact hnbonEF (between_same_line_out a g b EF ⟨hbet_ab, haonEF, hgonEF⟩)
  have hnsad : ¬(a.sameSide d EF) := by
    intro hsad
    have hdasymm := same_side_symm a d EF hsad
    have hdbsymm := same_side_symm b d EF hsameside
    exact hnsab (same_side_trans d a b EF ⟨hdasymm, hdbsymm⟩)
  exact ⟨hnaonEF, hndonEF, hnsad⟩

end Elements.Book1
