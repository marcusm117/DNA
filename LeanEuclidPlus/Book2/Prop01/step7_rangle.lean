import SystemE
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- Helper for 2.1.7: the angle ∠b:d:k is right. BF ∥ DK are cut by the transversal BC at the feet
   b and d; the co-interior angles sum to two right angles (proposition_29'''''):
   ∠g:b:d + ∠b:d:k = ∟ + ∟. Since g lies on the ray b→f' and ∠f:b:c = ∟ with d on segment b-c
   (between b d e, between d e c ⟹ between b d c), ∠g:b:d = ∠f:b:c = ∟, hence ∠b:d:k = ∟. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step7_rangle (b c d e f f' g k : Point) (BC BF DK GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hf'BF : f'.onLine BF)
    (hbff' : between b f f') (hbgf' : between b g f') (hfbc : ∠ f:b:c = ∟)
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hDKBF : ¬(DK.intersectsLine BF))
    (hgGH : g.onLine GH) (hkGH : k.onLine GH) (hGHBC : ¬(GH.intersectsLine BC)) :
    ∠ b:d:k = ∟ := by
  euclid_intros
  -- g and k are on the same side of BC (both on GH, which is parallel to BC)
  have hgsk : g.sameSide k BC := by
    have hgoff : ¬(g.onLine BC) := by euclid_finish
    have hkoff : ¬(k.onLine BC) := by euclid_finish
    by_contra hns
    euclid_apply (intersection_lines_opposing g k BC GH)
    euclid_finish
  -- co-interior angles: ∠g:b:d + ∠b:d:k = 2∟
  euclid_apply (proposition_29''''' g k b d BF DK BC)
  -- ∠g:b:d = ∠f:b:c = ∟ (d on segment b-c, g on ray b→f)
  euclid_finish

end Elements.Book2
