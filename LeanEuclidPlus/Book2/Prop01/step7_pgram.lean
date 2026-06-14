import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.7: b,g,d,k form a parallelogram with sides BF (b,g), DK (d,k), BC (b,d) and
   GH (g,k). The incidences are given; the remaining facts: g ≠ k on GH (distinct feet),
   b.sameSide d GH (both on BC, which is parallel to GH so does not cross it), BF ∦ DK (given),
   BC ∦ GH (given). f anchors BF ≠ BC; the off-GH facts come from BC ∥ GH; b ≠ d from between b d e. -/
theorem helper_2_1_step7_pgram (b d e f f' g k : Point) (BC BF DK GH : Line)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (hbde : between b d e)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hf'BF : f'.onLine BF) (hbgf' : between b g f')
    (hgGH : g.onLine GH) (hkGH : k.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hDKBF : ¬(DK.intersectsLine BF)) :
    formParallelogram b g d k BF DK BC GH := by
  euclid_intros
  have hgBF : g.onLine BF := by euclid_finish
  have hbsd : b.sameSide d GH := by
    have hboff : ¬(b.onLine GH) := by euclid_finish
    have hdoff : ¬(d.onLine GH) := by euclid_finish
    by_contra hns
    euclid_apply (intersection_lines_opposing b d GH BC)
    euclid_finish
  have hgk : g ≠ k := by euclid_finish
  euclid_finish

end Elements.Book2
