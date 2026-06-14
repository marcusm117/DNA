import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.9: the angle ∠e:c:h is right. BF ∥ CH are cut by the transversal BC at the feet
   b and c; the co-interior angles sum to two right angles (proposition_29'''''):
   ∠g:b:c + ∠b:c:h = ∟ + ∟. With ∠g:b:c = ∠f:b:c = ∟ (g on ray b→f', d,e,c collinear) this gives
   ∠b:c:h = ∟; and e lies on segment b-c (between b d e, between d e c), on c's b-side, so
   ∠e:c:h = ∠b:c:h = ∟. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step9_rangle (b c d e f f' g h : Point) (BC BF CH GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hf'BF : f'.onLine BF)
    (hbff' : between b f f') (hbgf' : between b g f') (hfbc : ∠ f:b:c = ∟)
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hCHBF : ¬(CH.intersectsLine BF))
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hGHBC : ¬(GH.intersectsLine BC)) :
    ∠ e:c:h = ∟ := by
  euclid_intros
  have hgsh : g.sameSide h BC := by
    have hgoff : ¬(g.onLine BC) := by euclid_finish
    have hhoff : ¬(h.onLine BC) := by euclid_finish
    by_contra hns
    euclid_apply (intersection_lines_opposing g h BC GH)
    euclid_finish
  euclid_apply (proposition_29''''' g h b c BF CH BC)
  euclid_finish

end Elements.Book2
