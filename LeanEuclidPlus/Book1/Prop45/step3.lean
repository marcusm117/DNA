import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step3
    (h m g l : Point) (HM GL GH LM : Line) (e₁ e₂ e₃ d b c : Point)
    (hh_HM : h.onLine HM) (hm_HM : m.onLine HM)
    (hg_GL : g.onLine GL) (hl_GL : l.onLine GL)
    (hh_GH : h.onLine GH) (hg_GH : g.onLine GH)
    (hm_LM : m.onLine LM) (hl_LM : l.onLine LM)
    (hh_side : h.sameSide g LM) (hml : m ≠ l)
    (hpar1 : ¬HM.intersectsLine GL) (hpar2 : ¬GH.intersectsLine LM)
    (hangle : ∠g:h:m = ∠e₁:e₂:e₃)
    (harea : Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) :
    formParallelogram h m g l HM GL GH LM ∧ (∠g:h:m = ∠e₁:e₂:e₃) ∧
      (Triangle.area △ g:h:m + Triangle.area △ g:l:m = Triangle.area △ d:b:c) :=
  ⟨by euclid_finish, hangle, harea⟩

end Elements.Book1
