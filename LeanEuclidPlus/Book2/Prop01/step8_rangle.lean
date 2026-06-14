import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.8: the angle ∠d:e:l is right. BF ∥ EL are cut by the transversal BC at the feet
   b and e; the co-interior angles sum to two right angles (proposition_29'''''):
   ∠g:b:e + ∠b:e:l = ∟ + ∟. With ∠g:b:e = ∠f:b:c = ∟ (g on ray b→f', e on segment b-c) this gives
   ∠b:e:l = ∟; and d lies on segment b-e (between b d e), on e's b-side, so ∠d:e:l = ∠b:e:l = ∟. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step8_rangle (b c d e f f' g l : Point) (BC BF EL GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hf'BF : f'.onLine BF)
    (hbff' : between b f f') (hbgf' : between b g f') (hfbc : ∠ f:b:c = ∟)
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hELBF : ¬(EL.intersectsLine BF))
    (hgGH : g.onLine GH) (hlGH : l.onLine GH) (hGHBC : ¬(GH.intersectsLine BC)) :
    ∠ d:e:l = ∟ := by
  euclid_intros
  have hgsl : g.sameSide l BC := by
    have hgoff : ¬(g.onLine BC) := by euclid_finish
    have hloff : ¬(l.onLine BC) := by euclid_finish
    by_contra hns
    euclid_apply (intersection_lines_opposing g l BC GH)
    euclid_finish
  euclid_apply (proposition_29''''' g l b e BF EL BC)
  euclid_finish

end Elements.Book2
