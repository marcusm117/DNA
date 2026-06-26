import SystemE
import Book2.Prop01.step5_dist
import Book2.Prop01.step5_offbc
import Book2.Prop01.step5_ss_bg_ch
import Book2.Prop01.step5_ss_bg_el
import Book2.Prop01.step5_ss_ch_el
import Book2.Prop01.step5_ss_bg_dk
import Book2.Prop01.step5_ss_el_dk
import Book2.Prop01.step5_btw_glh
import Book2.Prop01.step5_btw_gkl
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.5: rectangle BH (= B,C,H,G) equals BK + DL + EH.
   Strategy: cut BH by the EL vertical into BELG + ELHC, then cut BELG by the DK vertical into
   BDKG + DELK; the two sum_parallelograms_area equations telescope into the goal. The hard
   preconditions (the parallelogram sameSide facts and the foot betweennesses g-l-h, g-k-l) are
   derived as sub-nodes; the shared distinctness / off-base facts they rely on are bundled into
   step5_dist and step5_offbc (anchored on the perpendicular foot f, off BC). -/
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
  have step5_dist : b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ d ≠ e ∧ e ≠ c ∧ g.onLine BF ∧ ¬(g.onLine BC) := by euclid_apply (helper_2_1_step5_dist b c d e f f' g BC BF (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show f'.onLine BF; assumption)) (by euclid_assumption "" (show between b g f'; assumption)))
  obtain ⟨hbc, hbd, hbe, hde, hec, hgBF, hgoffBC⟩ := step5_dist
  -- the GH feet h, l, k lie off BC (GH ∥ BC, GH ≠ BC since g on GH is off BC)
  have step5_offbc : ¬(h.onLine BC) ∧ ¬(l.onLine BC) ∧ ¬(k.onLine BC) := by euclid_apply (helper_2_1_step5_offbc g h k l BC GH (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show ¬(g.onLine BC); assumption)) (by euclid_assumption "" (show ¬(GH.intersectsLine BC); assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show l.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)))
  obtain ⟨hhoffBC, hloffBC, hkoffBC⟩ := step5_offbc
  -- parallelogram sameSide preconditions: two points on a vertical lie on one side of a parallel vertical
  have step5_ss_bg_ch : b.sameSide g CH := by euclid_apply (helper_2_1_step5_ss_bg_ch b c f g BC BF CH (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show g.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BF); assumption)))
  have step5_ss_bg_el : b.sameSide g EL := by euclid_apply (helper_2_1_step5_ss_bg_el b e f g BC BF EL (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show g.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)))
  have step5_ss_ch_el : c.sameSide h EL := by euclid_apply (helper_2_1_step5_ss_ch_el b c e f h BC BF EL CH (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show e ≠ c; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show c.onLine CH; assumption)) (by euclid_assumption "" (show h.onLine CH; assumption)) (by euclid_assumption "" (show ¬(h.onLine BC); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(CH.intersectsLine BF); assumption)))
  have step5_ss_bg_dk : b.sameSide g DK := by euclid_apply (helper_2_1_step5_ss_bg_dk b d f g BC BF DK (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show g.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show d.onLine DK; assumption)) (by euclid_assumption "" (show ¬(DK.intersectsLine BF); assumption)))
  have step5_ss_el_dk : e.sameSide l DK := by euclid_apply (helper_2_1_step5_ss_el_dk b d e f k l BC BF DK EL (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ d; assumption)) (by euclid_assumption "" (show b ≠ e; assumption)) (by euclid_assumption "" (show d ≠ e; assumption)) (by euclid_assumption "" (show b.onLine BF; assumption)) (by euclid_assumption "" (show f.onLine BF; assumption)) (by euclid_assumption "" (show ¬(f.onLine BC); assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show l.onLine EL; assumption)) (by euclid_assumption "" (show ¬(l.onLine BC); assumption)) (by euclid_assumption "" (show d.onLine DK; assumption)) (by euclid_assumption "" (show k.onLine DK; assumption)) (by euclid_assumption "" (show ¬(k.onLine BC); assumption)) (by euclid_assumption "" (show ¬(DK.intersectsLine BF); assumption)) (by euclid_assumption "" (show ¬(EL.intersectsLine BF); assumption)))
  -- foot order on GH mirrors top order b-d-e-c on BC, via pasch_4
  have step5_btw_glh : between g l h := by euclid_apply (helper_2_1_step5_btw_glh b c d e g h l BC GH EL (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show between d e c; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show l.onLine GH; assumption)) (by euclid_assumption "" (show e.onLine EL; assumption)) (by euclid_assumption "" (show l.onLine EL; assumption)) (by euclid_assumption "" (show b.sameSide g EL; assumption)) (by euclid_assumption "" (show c.sameSide h EL; assumption)))
  have step5_btw_gkl : between g k l := by euclid_apply (helper_2_1_step5_btw_gkl b d e g k l BC GH DK (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show d.onLine BC; assumption)) (by euclid_assumption "" (show e.onLine BC; assumption)) (by euclid_assumption "" (show between b d e; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show k.onLine GH; assumption)) (by euclid_assumption "" (show l.onLine GH; assumption)) (by euclid_assumption "" (show d.onLine DK; assumption)) (by euclid_assumption "" (show k.onLine DK; assumption)) (by euclid_assumption "" (show b.sameSide g DK; assumption)) (by euclid_assumption "" (show e.sameSide l DK; assumption)))
  euclid_apply (sum_parallelograms_area b c g h e l BC GH BF CH)
  euclid_apply (sum_parallelograms_area b e g l d k BC GH BF EL)
  euclid_finish

end Elements.Book2
