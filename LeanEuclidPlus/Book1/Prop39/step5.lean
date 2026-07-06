import SystemE
import Book1.Prop37.variants
import Book1.Prop39.step5_triEBC
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_39_step5
    (a b c d e : Point) (AB BC AC BD CD EC AE : Line)
    -- triangle abc
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (habne : a ≠ b)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcAC : c.onLine AC) (haAC : a.onLine AC)
    (hABBC : AB ≠ BC) (hBCAC : BC ≠ AC) (hACAB : AC ≠ AB)
    -- triangle dbc
    (hdBD : d.onLine BD) (hbBD : b.onLine BD) (hdbne : d ≠ b) (hcCD : c.onLine CD) (hdCD : d.onLine CD)
    (hBDBC : BD ≠ BC) (hBCCD : BC ≠ CD) (hCDBD : CD ≠ BD)
    -- triangle ebc atoms
    (heBD : e.onLine BD) (hcEC : c.onLine EC) (heEC : e.onLine EC)
    -- same-side (used by step5_triEBC)
    (hasdBC : a.sameSide d BC)
    -- both apexes on parallel AE
    (haAE : a.onLine AE) (heAE : e.onLine AE)
    -- @assumption ("on the same base as it, $BC$, and between the same parallels", ¬(AE.intersectsLine BC))
    (hassump1 : ¬(AE.intersectsLine BC))
    : Triangle.area △ a:b:c = Triangle.area △ e:b:c := by
  by_cases hane : a = e
  · subst hane; rfl
  · have step5_triEBC : formTriangle e b c BD BC EC := by euclid_apply (helper_1_39_step5_triEBC a e b c d BD BC EC AE CD (by euclid_assumption "" (show e.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BD; assumption)) (by euclid_assumption "" (show d.onLine BD; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine EC; assumption)) (by euclid_assumption "" (show e.onLine EC; assumption)) (by euclid_assumption "" (show BD ≠ BC; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show d.onLine CD; assumption)) (by euclid_assumption "" (show CD ≠ BD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show a.onLine AE; assumption)) (by euclid_assumption "" (show e.onLine AE; assumption)) (by euclid_assumption "" (show ¬(AE.intersectsLine BC); assumption)) (by euclid_assumption "" (show a.sameSide d BC; assumption)))
    have step5_distAE : distinctPointsOnLine a e AE := ⟨haAE, heAE, hane⟩
    euclid_apply (proposition_37' a b c e AB BC AC BD EC AE)
    euclid_finish

end Elements.Book1
