import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.7: CM = DF. By adding DM to both sides of step6 (CH = HF).
   (1) sum_parallelograms_area on par c b l m (rect CM, bottom AB, top KM, left CE, right BF),
       cut at d (between c and b on AB) and h (between l and m on KM): CM = CH + DM.
   (2) sum_parallelograms_area on par d g b f (rect DF, left DG, right BF, bottom AB, top EF),
       cut at h (between d and g on DG) and m (between b and f on BF): DF = DM + HF.
   Since CH = HF (hstep6), CM = DF.
   step7_cmpar, step7_dfpar, step7_lhm, step7_dhg, step7_bmf are Main-level nodes (proved in their
   own backing files) and passed in as hypotheses here, making this a leaf. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step7 (c d b f g h l m : Point) (AB KM CE BF DG EF : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB) (hbAB : b.onLine AB)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM) (hmKM : m.onLine KM)
    (hcCE : c.onLine CE) (hlCE : l.onLine CE)
    (hbBF : b.onLine BF) (hmBF : m.onLine BF) (hfBF : f.onLine BF)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG) (hgDG : g.onLine DG)
    (hgEF : g.onLine EF) (hfEF : f.onLine EF)
    (hcdb : between c d b)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hCEBF : ¬(CE.intersectsLine BF))
    (hEFAB : ¬(EF.intersectsLine AB))
    (hstep6 : Triangle.area △ c:d:h + Triangle.area △ c:h:l =
               Triangle.area △ h:m:f + Triangle.area △ h:f:g)
    (hcmpar : formParallelogram c b l m AB KM CE BF)
    (hdfpar : formParallelogram d g b f DG BF AB EF)
    (hlhm : between l h m)
    (hdhg : between d h g)
    (hbmf : between b m f) :
    Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ d:b:f + Triangle.area △ d:f:g := by
  euclid_intros
  euclid_apply (sum_parallelograms_area c b l m d h AB KM CE BF)
  euclid_apply (sum_parallelograms_area d g b f h m DG BF AB EF)
  euclid_finish
  

end Elements.Book2
