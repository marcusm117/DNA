import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_45_step2
    (f g k h : Point) (FG KH FK GH : Line) (e₁ e₂ e₃ a b d : Point)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG)
    (hk_KH : k.onLine KH) (hh_KH : h.onLine KH)
    (hf_FK : f.onLine FK) (hk_FK : k.onLine FK)
    (hg_GH : g.onLine GH) (hh_GH : h.onLine GH)
    (hf_side : f.sameSide k GH) (hgh : g ≠ h)
    (hpar1 : ¬FG.intersectsLine KH) (hpar2 : ¬FK.intersectsLine GH)
    (hangle : ∠h:k:f = ∠e₁:e₂:e₃)
    (harea : Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d) :
    formParallelogram f g k h FG KH FK GH ∧ (∠h:k:f = ∠e₁:e₂:e₃) ∧
      (Triangle.area △ f:k:h + Triangle.area △ f:h:g = Triangle.area △ a:b:d) :=
  ⟨by euclid_finish, hangle, harea⟩

end Elements.Book1
