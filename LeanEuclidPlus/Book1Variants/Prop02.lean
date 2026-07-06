import SystemE
import Book1Variants.Prop01
import Book1.Prop02.Main

namespace Elements.Book1

theorem proposition_2' : ∀ (a b c : Point) (BC : Line),
  distinctPointsOnLine b c BC →
  ∃ l : Point, |(a─l)| = |(b─c)| :=
by
  euclid_intros
  by_cases (a = b)
  . use c
    euclid_finish
  . euclid_apply proposition_2 a b c BC as l
    use l

end Elements.Book1
