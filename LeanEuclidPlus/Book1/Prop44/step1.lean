import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_44_step1
    (f g b e : Point) (GF AB BG EF : Line)
    (hfGF : f.onLine GF) (hgGF : g.onLine GF)
    (hbAB : b.onLine AB) (heAB : e.onLine AB)
    (hfBG : f.onLine BG) (hbBG : b.onLine BG)
    (hgEF : g.onLine EF) (heEF : e.onLine EF)
    (hside : f.sameSide b EF)
    (hge : g ≠ e)
    (hGFAB : ¬GF.intersectsLine AB)
    (hBGEF : ¬BG.intersectsLine EF)
    (hangle : ∠ e:b:f = ∠ d₁:d₂:d₃)
    (harea : (△f:b:e).area + (△f:e:g).area = (△c₁:c₂:c₃).area)
    : formParallelogram f g b e GF AB BG EF ∧ ∠ e:b:f = ∠ d₁:d₂:d₃ ∧
      Triangle.area △ f:b:e + Triangle.area △ f:e:g = Triangle.area △ c₁:c₂:c₃ := by
  exact ⟨by euclid_finish, hangle, harea⟩

end Elements.Book1
