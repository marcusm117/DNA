import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step17_assumption2
    (h m g l : Point) (HM GL GH LM : Line)
    (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hh_GH : h.onLine GH) (hg_GH : g.onLine GH)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM) (hml : m ≠ l)
    (hh_sg_LM : h.sameSide g LM)
    (hpar_HM_GL : ¬HM.intersectsLine GL)
    (hpar_GH_LM : ¬GH.intersectsLine LM) :
    |(h─g)| = |(m─l)| ∧ ¬GH.intersectsLine LM := by
  have hpgram : formParallelogram h m g l HM GL GH LM :=
    ⟨hh_HM, hm_HM, hg_GL, hl_GL, hh_GH, hg_GH,
     ⟨hm_LM, hl_LM, hml⟩, hh_sg_LM, hpar_HM_GL, hpar_GH_LM⟩
  euclid_apply (proposition_34' h m g l HM GL GH LM hpgram)
  constructor
  · euclid_finish
  · exact hpar_GH_LM

end Elements.Book1
