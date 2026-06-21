import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.7 sub: between d m f. m = KM ∩ DF; d (on AB, above KM) and f (on EF, below KM) are the two
   ends of the square side DF, so the crossing m lies between them. d, f are on opposite sides of KM
   (step7_dnsf: ¬d.sameSide f KM); KM ≠ DF since h ∈ KM, ¬h ∈ DF. pasch_4 on d, m, f across KM and DF
   (m the common point) gives between d m f. Distinctness: d ≠ f (d ∈ AB, ¬f ∈ AB); d ≠ m (m ∈ KM,
   ¬d ∈ KM via d ∈ AB, ¬h-style — here from ¬d.onLine KM); f ≠ m (m ∈ KM, ¬f ∈ KM). -/
theorem helper_2_6_step7_dmf (d f h m : Point) (AB KM DF : Line)
    (hdDF : d.onLine DF) (hfDF : f.onLine DF) (hmDF : m.onLine DF)
    (hmKM : m.onLine KM) (hhKM : h.onLine KM) (hdAB : d.onLine AB)
    (hhoffDF : ¬(h.onLine DF)) (hfoffAB : ¬(f.onLine AB))
    (hdoffKM : ¬(d.onLine KM)) (hfoffKM : ¬(f.onLine KM))
    (hdnsf : ¬(d.sameSide f KM)) :
    between d m f := by
  euclid_intros
  have hKMneDF : KM ≠ DF := fun heq => hhoffDF (heq ▸ hhKM)
  have hdf : d ≠ f := fun heq => hfoffAB (heq ▸ hdAB)
  have hdm : d ≠ m := fun heq => hdoffKM (heq ▸ hmKM)
  have hfm : f ≠ m := fun heq => hfoffKM (heq ▸ hmKM)
  euclid_apply (pasch_4 d m f KM DF)
  euclid_finish

end Elements.Book2
