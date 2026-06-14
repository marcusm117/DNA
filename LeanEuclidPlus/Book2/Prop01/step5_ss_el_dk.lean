import SystemE
import Book2.Prop01.step5_ss_el_dk_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.5: e and l (both on the EL vertical) are on the same side of the DK vertical.
   EL ∦ DK (sub-node step5_ss_el_dk_par, via proposition_30 since both ∦ BF). e,l are off DK
   (a common point of DK and EL would force them to meet, contradicting DK ∦ EL — DK ≠ EL since
   d ≠ e sits on DK∩BC while e on EL is off DK). Being off DK and not separable across it, e and
   l share a side. -/
theorem helper_2_1_step5_ss_el_dk (b d e f k l : Point) (BC BF DK EL : Line)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hloffBC : ¬(l.onLine BC))
    (hdDK : d.onLine DK) (hkDK : k.onLine DK) (hkoffBC : ¬(k.onLine BC))
    (hDKBF : ¬(DK.intersectsLine BF)) (hELBF : ¬(EL.intersectsLine BF)) :
    e.sameSide l DK := by
  euclid_intros
  have step5_ss_el_dk_par : ¬(EL.intersectsLine DK) := by euclid_apply (helper_2_1_step5_ss_el_dk_par b d e f k l BC BF DK EL (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have heoff : ¬(e.onLine DK) := by
    by_contra heon
    euclid_apply (intersection_lines_common_point e DK EL)
    euclid_finish
  have hloff : ¬(l.onLine DK) := by
    by_contra hlon
    euclid_apply (intersection_lines_common_point l DK EL)
    euclid_finish
  by_contra hns
  euclid_apply (intersection_lines_opposing e l DK EL)
  euclid_finish

end Elements.Book2
