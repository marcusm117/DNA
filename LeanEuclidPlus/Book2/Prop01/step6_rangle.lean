import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.6: the angle ∠b:c:h is right. BF ∥ CH are cut by the transversal BC at the feet
   b and c; the co-interior angles sum to two right angles (proposition_29'''''):
   ∠g:b:c + ∠b:c:h = ∟ + ∟. Since g lies on the ray b→f (between b g f', between b f f'),
   ∠g:b:c = ∠f:b:c = ∟, hence ∠b:c:h = ∟. g.sameSide h BC (both feet's verticals rise to GH on
   one side of BC). -/
theorem helper_2_1_step6_rangle (b c f f' g h : Point) (BC BF CH GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hbc : b ≠ c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hf'BF : f'.onLine BF)
    (hbff' : between b f f') (hbgf' : between b g f') (hfbc : ∠ f:b:c = ∟)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hCHBF : ¬(CH.intersectsLine BF))
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hGHBC : ¬(GH.intersectsLine BC)) :
    ∠ b:c:h = ∟ := by
  euclid_intros
  -- g and h are on the same side of BC (both on GH, which is parallel to BC)
  have hgsh : g.sameSide h BC := by
    have hgoff : ¬(g.onLine BC) := by euclid_finish
    have hhoff : ¬(h.onLine BC) := by euclid_finish
    by_contra hns
    euclid_apply (intersection_lines_opposing g h BC GH)
    euclid_finish
  -- co-interior angles: ∠g:b:c + ∠b:c:h = 2∟
  euclid_apply (proposition_29''''' g h b c BF CH BC)
  -- ∠g:b:c = ∠f:b:c = ∟ since g is on the ray b→f
  euclid_finish

end Elements.Book2
