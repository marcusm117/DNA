import SystemE
import Book.Prop03
import Book.Prop11
import Book.Prop29
import Book.Prop30
import Book.Prop31
import Book.Prop34

namespace Elements.Book2

open Elements.Book1

theorem proposition_1 : ∀ (a₁ a₂ b c d e : Point) (A BC : Line),
  distinctPointsOnLine a₁ a₂ A ∧ distinctPointsOnLine b c BC ∧
  d.onLine BC ∧ e.onLine BC ∧ between b d e ∧ between d e c →
  |(a₁─a₂)| * |(b─c)| =
    |(a₁─a₂)| * |(b─d)| + |(a₁─a₂)| * |(d─e)| + |(a₁─a₂)| * |(e─c)| :=
by
  sorry
end Elements.Book2
