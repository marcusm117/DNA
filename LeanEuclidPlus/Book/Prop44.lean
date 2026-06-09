import SystemE
import Book.Prop15
import Book.Prop29
import Book.Prop30
import Book.Prop31
import Book.Prop42
import Book.Prop43


namespace Elements.Book1

/-- Helper for `proposition_44`/`proposition_44'`: the precondition `between h a l` of
`proposition_43` cannot be auto-discharged by `euclid_apply` in the full proof context (the
solver stalls on the bloated context).  Proven in isolation here: `h ∈ FG ∥ AB` and `l ∈ KL ∥ AB`
sit on opposite sides of `AB`, with `a` on both `AB` and `AH`, so `pasch_4` gives `between h a l`. -/
theorem helper_44_between_hal :
    ∀ (a b e g f h k l m : Point) (AB FG BG EF AH HB KL : Line),
    a.onLine AB ∧ b.onLine AB ∧ a ≠ b ∧
    between a b e ∧
    g.onLine FG ∧ f.onLine FG ∧
    b.onLine AB ∧ e.onLine AB ∧
    g.onLine BG ∧ b.onLine BG ∧
    f.onLine EF ∧ e.onLine EF ∧
    g.sameSide b EF ∧
    f ≠ e ∧
    ¬FG.intersectsLine AB ∧
    ¬BG.intersectsLine EF ∧
    a.onLine AH ∧
    ¬AH.intersectsLine BG ∧
    ¬AH.intersectsLine EF ∧
    h.onLine AH ∧ h.onLine FG ∧
    h.onLine HB ∧ b.onLine HB ∧
    k.onLine HB ∧ k.onLine EF ∧
    k.onLine KL ∧
    ¬KL.intersectsLine AB ∧
    ¬KL.intersectsLine FG ∧
    l.onLine AH ∧ l.onLine KL ∧
    m.onLine BG ∧ m.onLine KL →
    between h a l :=
by
  euclid_intros
  euclid_assert ¬(h.onLine AB)
  euclid_assert ¬(l.onLine AB)
  euclid_assert ¬(h.sameSide l AB)
  euclid_apply (pasch_4 h a l AB AH)
  euclid_finish

/-- Companion to `helper_44_between_hal`: the precondition `between g b m` of `proposition_15` is
likewise not auto-dischargeable in the full proof context.  Same geometry on line `BG`:
`g ∈ FG ∥ AB` and `m ∈ KL ∥ AB` are on opposite sides of `AB`, `b` on both `AB` and `BG`. -/
theorem helper_44_between_gbm :
    ∀ (a b e g f h k l m : Point) (AB FG BG EF AH HB KL : Line),
    a.onLine AB ∧ b.onLine AB ∧ a ≠ b ∧
    between a b e ∧
    g.onLine FG ∧ f.onLine FG ∧
    b.onLine AB ∧ e.onLine AB ∧
    g.onLine BG ∧ b.onLine BG ∧
    f.onLine EF ∧ e.onLine EF ∧
    g.sameSide b EF ∧
    f ≠ e ∧
    ¬FG.intersectsLine AB ∧
    ¬BG.intersectsLine EF ∧
    a.onLine AH ∧
    ¬AH.intersectsLine BG ∧
    ¬AH.intersectsLine EF ∧
    h.onLine AH ∧ h.onLine FG ∧
    h.onLine HB ∧ b.onLine HB ∧
    k.onLine HB ∧ k.onLine EF ∧
    k.onLine KL ∧
    ¬KL.intersectsLine AB ∧
    ¬KL.intersectsLine FG ∧
    l.onLine AH ∧ l.onLine KL ∧
    m.onLine BG ∧ m.onLine KL →
    between g b m :=
by
  euclid_intros
  euclid_assert ¬(g.onLine AB)
  euclid_assert ¬(m.onLine AB)
  euclid_assert ¬(g.sameSide m AB)
  euclid_apply (pasch_4 g b m AB BG)
  euclid_finish

theorem proposition_44 : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m = ∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m + Triangle.area △ a:l:m = Triangle.area △ c₁:c₂:c₃) :=
by
  euclid_intros
  euclid_apply (proposition_42'' c₁ c₂ c₃ d₁ d₂ d₃ a b C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ AB) as (g, f, e, FG, BG, EF)
  euclid_apply (proposition_31 a b g BG) as AH
  euclid_apply (proposition_30 AH EF BG)
  euclid_apply (intersection_lines AH FG) as h
  euclid_apply (line_from_points h b) as HB
  euclid_apply (proposition_29''''' e a f h EF AH FG)
  euclid_apply (intersection_lines HB EF) as k
  euclid_apply (proposition_31 k e a AB) as KL
  euclid_apply (proposition_30 KL FG AB)
  euclid_apply (intersection_lines AH KL) as l
  euclid_apply (intersection_lines BG KL) as m
  -- `between h a l` (precond of proposition_43) is not auto-dischargeable in this context; supply it.
  euclid_apply (helper_44_between_hal a b e g f h k l m AB FG BG EF AH HB KL)
  euclid_apply (proposition_43 h f k l g m e a b AH EF FG KL HB BG AB)
  -- `between g b m` (precond of proposition_15) likewise needs supplying in this context.
  euclid_apply (helper_44_between_gbm a b e g f h k l m AB FG BG EF AH HB KL)
  euclid_apply (proposition_15 e a m g b AB BG)
  use m, l, BG, AH, KL
  euclid_finish

theorem proposition_44' : ∀ (a b c₁ c₂ c₃ d₁ d₂ d₃ x : Point) (AB C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ : Line),
  formTriangle c₁ c₂ c₃ C₁₂ C₂₃ C₃₁ ∧ formRectilinearAngle d₁ d₂ d₃ D₁₂ D₂₃ ∧ distinctPointsOnLine a b AB ∧ ¬(x.onLine AB) ∧
  (∠ d₁:d₂:d₃ : ℝ) > 0 ∧ (∠ d₁:d₂:d₃ : ℝ) < ∟ + ∟ →
  ∃ (m l : Point) (BM AL ML : Line), Point.opposingSides m x AB ∧ formParallelogram b m a l BM AL AB ML ∧
  (∠ a:b:m : ℝ) = (∠ d₁:d₂:d₃) ∧ (Triangle.area △ a:b:m) + (Triangle.area △ a:l:m) = (Triangle.area △ c₁:c₂:c₃) :=
by
  euclid_intros
  euclid_apply (proposition_42''' c₁ c₂ c₃ d₁ d₂ d₃ a b x C₁₂ C₂₃ C₃₁ D₁₂ D₂₃ AB) as (g, f ,e ,FG, BG, EF)
  euclid_apply (proposition_31 a b g BG) as AH
  euclid_apply (proposition_30 AH EF BG)
  euclid_apply (intersection_lines AH FG) as h
  euclid_apply (line_from_points h b) as HB
  euclid_apply (proposition_29''''' e a f h EF AH FG)
  euclid_apply (intersection_lines HB EF) as k
  euclid_apply (proposition_31 k e a AB) as KL
  euclid_apply (proposition_30 KL FG AB)
  euclid_apply (intersection_lines AH KL) as l
  euclid_apply (intersection_lines BG KL) as m
  -- `between h a l` (precond of proposition_43) is not auto-dischargeable in this context; supply it.
  euclid_apply (helper_44_between_hal a b e g f h k l m AB FG BG EF AH HB KL)
  euclid_apply (proposition_43 h f k l g m e a b AH EF FG KL HB BG AB)
  -- `between g b m` (precond of proposition_15) likewise needs supplying in this context.
  euclid_apply (helper_44_between_gbm a b e g f h k l m AB FG BG EF AH HB KL)
  euclid_apply (proposition_15 e a m g b AB BG)
  use m, l, BG, AH, KL
  euclid_finish

end Elements.Book1
