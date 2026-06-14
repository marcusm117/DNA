import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.6: b,g,c,h form a parallelogram with sides BF (b,g), CH (c,h), BC (b,c) and
   GH (g,h). The incidences are given; the remaining facts: g ≠ h on GH (distinct feet),
   b.sameSide c GH (both on BC, which is parallel to GH so does not cross it), BF ∦ CH (given),
   BC ∦ GH (given). f anchors BF ≠ BC; the off-GH facts come from BC ∥ GH. -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step6_pgram (b c f f' g h : Point) (BC BF CH GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hbc : b ≠ c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hf'BF : f'.onLine BF) (hbgf' : between b g f')
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hCHBF : ¬(CH.intersectsLine BF)) :
    formParallelogram b g c h BF CH BC GH := by
  euclid_intros
  have hgBF : g.onLine BF := by euclid_finish
  -- b and c are on the same side of GH (both on BC, which is parallel to GH)
  have hbsc : b.sameSide c GH := by
    have hboff : ¬(b.onLine GH) := by euclid_finish
    have hcoff : ¬(c.onLine GH) := by euclid_finish
    by_contra hns
    euclid_apply (intersection_lines_opposing b c GH BC)
    euclid_finish
  -- g ≠ h: g,h on GH; if g = h then h on BF, but h on CH ∦ BF
  have hgh : g ≠ h := by euclid_finish
  euclid_finish

end Elements.Book2
