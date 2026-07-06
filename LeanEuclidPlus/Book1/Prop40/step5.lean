import SystemE
import Book1.Prop38.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_40_step5
    (a b c f e : Point) (AB BC AC CD AF FE : Line)
    -- first triangle abc
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (habne : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    -- second triangle fce
    (hfCD : f.onLine CD) (hcCD : c.onLine CD)
    (heBC : e.onLine BC) (hfFE : f.onLine FE) (heFE : e.onLine FE)
    (hCDBC : CD ≠ BC)
    -- both apexes on parallel AF
    (haAF : a.onLine AF) (hfAF : f.onLine AF)
    -- equal bases
    (hbene : b ≠ e)
    -- @assumption binders
    (hassump1 : |(b─c)| = |(c─e)|)
    (hassump2 : ¬(AF.intersectsLine BC)) :
    Triangle.area △ a:b:c = Triangle.area △ f:c:e := by
  have hbet : between b c e := by euclid_finish
  euclid_apply (proposition_38 a b c f c e AF BC AB AC CD FE)
  euclid_finish

end Elements.Book1
