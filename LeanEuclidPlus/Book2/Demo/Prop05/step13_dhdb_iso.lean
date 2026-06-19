import SystemE
import Book.Prop05
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.13 sub: ∠ c:e:b = ∠ c:b:e. Triangle CEB is isosceles — |c─e| = |c─b| (the square's two sides
   from C) — with CE (c,e), BE (e,b), AB (b,c) forming it and ∠ b:c:e = ∟ pinning non-collinearity,
   so its base angles at E and B are equal [Prop.~1.5]. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step13_dhdb_iso (b c e : Point) (AB CE BE : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hce_cb : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟)
    (hcb : c ≠ b) (hce : c ≠ e) (heb : e ≠ b) (hcoffBE : ¬(c.onLine BE)) :
    ∠ c:e:b = ∠ c:b:e := by
  euclid_intros
  -- triangle CEB: CE (c,e), BE (e,b), AB (b,c), pairwise distinct
  have hCEBE : CE ≠ BE := fun heq => hcoffBE (heq ▸ hcCE)
  have hCEAB : CE ≠ AB := by
    intro heq
    -- if CE = AB then e ∈ AB and b,c ∈ AB; ∠ b:c:e = ∟ with all collinear is impossible
    euclid_finish
  have hBEAB : BE ≠ AB := fun heq => hcoffBE (heq ▸ hcAB)
  have htri : formTriangle c e b CE BE AB := by
    unfold formTriangle
    repeat' apply And.intro
    all_goals first | assumption | euclid_finish
  euclid_apply (proposition_5' c e b CE BE AB)
  euclid_finish

end Elements.Book2
