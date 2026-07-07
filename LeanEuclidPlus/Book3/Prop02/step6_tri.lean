import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step6_tri (a d p : Point) (DA DFE AP : Line)
    (hdDA : d.onLine DA) (haDA : a.onLine DA)
    (hdDFE : d.onLine DFE) (hpDFE : p.onLine DFE)
    (haAP : a.onLine AP) (hpAP : p.onLine AP)
    (hda_ne : d ≠ a) (hap_ne : a ≠ p)
    (hd_AP : ¬d.onLine AP) :
    formTriangle d a p DA AP DFE := by
  have hDA_ne_AP : DA ≠ AP := fun h => absurd (h ▸ hdDA) hd_AP
  have hAP_ne_DFE : AP ≠ DFE := fun h => absurd (h.symm ▸ hdDFE) hd_AP
  have hDFE_ne_DA : DFE ≠ DA := by
    intro hEQ
    have haonDFE : a.onLine DFE := hEQ.symm ▸ haDA
    have hDisAP : distinctPointsOnLine a p AP := by euclid_finish
    have hAPeqDFE : AP = DFE :=
      two_points_determine_line a p AP DFE ⟨hDisAP, haonDFE, hpDFE⟩
    exact hd_AP (hAPeqDFE.symm ▸ hdDFE)
  euclid_finish

end Elements.Book3
