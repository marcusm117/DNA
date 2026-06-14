import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.5: rectangle BH (= B,C,H,G) equals BK + DL + EH.
   Strategy: cut BH by the EL vertical into BELG + ELHC, then cut BELG by the DK vertical into
   BDKG + DELK; the two sum_parallelograms_area equations telescope into the goal. The hard
   preconditions (the parallelogram sameSide facts and the foot betweennesses g-l-h, g-k-l) are
   derived as sub-nodes; the shared distinctness / off-base facts they rely on are bundled into
   step5_dist and step5_offbc (anchored on the perpendicular foot f, off BC). -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step5 (b c d e f f' g h k l : Point) (BC GH BF DK EL CH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hf'BF : f'.onLine BF) (hbgf' : between b g f')
    (hgGH : g.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (hdDK : d.onLine DK) (hDKBF : ¬(DK.intersectsLine BF))
    (heEL : e.onLine EL) (hELBF : ¬(EL.intersectsLine BF))
    (hcCH : c.onLine CH) (hCHBF : ¬(CH.intersectsLine BF))
    (hkDK : k.onLine DK) (hkGH : k.onLine GH)
    (hlEL : l.onLine EL) (hlGH : l.onLine GH)
    (hhCH : h.onLine CH) (hhGH : h.onLine GH) :
    Triangle.area △ b:c:h + Triangle.area △ b:g:h =
      (Triangle.area △ b:d:k + Triangle.area △ b:g:k)
    + (Triangle.area △ d:e:l + Triangle.area △ d:k:l)
    + (Triangle.area △ e:c:h + Triangle.area △ e:l:h) := by
  euclid_intros
  -- shared distinctness + g on BF / off BC (anchored on f off BC)
  have step5_dist : b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e ∧ e ≠ c ∧ g.onLine BF ∧ ¬(g.onLine BC) := by sorry
  obtain ⟨hbc, hbd, hbe, hde, hec, hgBF, hgoffBC⟩ := step5_dist
  -- the GH feet h, l, k lie off BC (GH ∥ BC, GH ≠ BC since g on GH is off BC)
  have step5_offbc : ¬(h.onLine BC) ∧ ¬(l.onLine BC) ∧ ¬(k.onLine BC) := by sorry
  obtain ⟨hhoffBC, hloffBC, hkoffBC⟩ := step5_offbc
  -- parallelogram sameSide preconditions: two points on a vertical lie on one side of a parallel vertical
  have step5_ss_bg_ch : b.sameSide g CH := by sorry
  have step5_ss_bg_el : b.sameSide g EL := by sorry
  have step5_ss_ch_el : c.sameSide h EL := by sorry
  have step5_ss_bg_dk : b.sameSide g DK := by sorry
  have step5_ss_el_dk : e.sameSide l DK := by sorry
  -- foot order on GH mirrors top order b-d-e-c on BC, via pasch_4
  have step5_btw_glh : between g l h := by sorry
  have step5_btw_gkl : between g k l := by sorry
  euclid_apply (sum_parallelograms_area b c g h e l BC GH BF CH)
  euclid_apply (sum_parallelograms_area b e g l d k BC GH BF EL)
  euclid_finish

end Elements.Book2
