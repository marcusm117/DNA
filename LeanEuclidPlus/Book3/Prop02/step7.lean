import SystemE
import Book3.Prop02.step7_inside
import Book3.Prop02.step7_tri
import Book3.Prop02.step7_base
import Book3.Prop02.step7_eq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step7 (a b d p : Point) (ABC : Circle) (DA DB : Line)
    (ha : a.onCircle ABC) (hb : b.onCircle ABC) (hd : d.isCentre ABC)
    (hdDA : d.onLine DA) (haDA : a.onLine DA)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (hda_ne : d ≠ a) (hdb_ne : d ≠ b) (hab : a ≠ b)
    (hbet : between a p b)
    (hnotinside : ¬p.insideCircle ABC)
    (hassump1 : |(d─a)| = |(d─b)|) :
    ∠ d:a:p = ∠ d:b:p := by
  euclid_apply (line_from_points a b) as AB
  by_cases hd_AB : d.onLine AB
  · -- @args: a b p ABC
    have step7_inside : p.insideCircle ABC := by euclid_apply (helper_3_2_step7_inside a b p ABC (by euclid_assumption "" (show a.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show between a p b; assumption)))
    exact absurd step7_inside hnotinside
  ·
    -- @args: a b d DA DB AB
    have step7_tri : formTriangle d a b DA AB DB := by euclid_apply (helper_3_2_step7_tri a b d DA DB AB (by euclid_assumption "" (show d.onLine DA; assumption)) (by euclid_assumption "" (show a.onLine DA; assumption)) (by euclid_assumption "" (show d.onLine DB; assumption)) (by euclid_assumption "" (show b.onLine DB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show b.onLine AB; assumption)) (by euclid_assumption "" (show d ≠ a; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show a ≠ b; assumption)) (by euclid_assumption "" (show ¬d.onLine AB; assumption)))
    -- @args: a b d DA AB DB
    have step7_base : ∠ d:a:b = ∠ d:b:a := by euclid_apply (helper_3_2_step7_base a b d DA AB DB (by euclid_assumption "" (show formTriangle d a b DA AB DB; assumption)) (by euclid_assumption "" (show |(d─a)| = |(d─b)|; assumption)))
    -- @args: a b d p DA AB DB
    have step7_eq : ∠ d:a:p = ∠ d:b:p := by euclid_apply (helper_3_2_step7_eq a b d p DA AB DB (by euclid_assumption "" (show formTriangle d a b DA AB DB; assumption)) (by euclid_assumption "" (show ∠ d:a:b = ∠ d:b:a; assumption)) (by euclid_assumption "" (show between a p b; assumption)))
    exact step7_eq

end Elements.Book3
