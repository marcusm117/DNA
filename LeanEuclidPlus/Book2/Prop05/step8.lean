import SystemE
import Book.Prop36
import Book2.Prop05.step8_alpar_kss
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.8: CM = AL since AC = CB [Prop.~1.36]. Both rectangles between parallels AB and KM.
   hcmpar (= step7_cmpar from Main) provides CM's parallelogram.
   step8_alpar_kss proves k.sameSide a CE (needs betweenness hacd to derive a∉CE → AK≠CE).
   proposition_36' (l c b m k a c l KM AB CE BF AK CE) with euclid_finish closes the area goal. -/
theorem helper_2_5_step8 (a b c d k l m : Point) (AB KM AK CE BF : Line)
    (hacb_len : |(a─c)| = |(c─b)|)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hkKM : k.onLine KM) (hlKM : l.onLine KM) (hmKM : m.onLine KM)
    (hkAK : k.onLine AK) (haAK : a.onLine AK)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE)
    (hmBF : m.onLine BF) (hbBF : b.onLine BF)
    (hacd : between a c d)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hAKCE : ¬(AK.intersectsLine CE))
    (hCEBF : ¬(CE.intersectsLine BF))
    (hcmpar : formParallelogram c b l m AB KM CE BF) :
    Triangle.area △ c:b:m + Triangle.area △ c:m:l =
      Triangle.area △ a:c:l + Triangle.area △ a:l:k := by
  euclid_intros
  have step8_alpar_kss : k.sameSide a CE := by euclid_apply (helper_2_5_step8_alpar_kss a b c d k l m AB KM AK CE BF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have h_base : |(c─b)| = |(a─c)| := by euclid_finish
  euclid_apply (proposition_36' l c b m k a c l KM AB CE BF AK CE)
  euclid_finish

end Elements.Book2
