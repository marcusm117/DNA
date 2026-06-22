import SystemE
import Book2.Prop07.step13_cut1
import Book2.Prop07.step13_cutL
import Book2.Prop07.step13_cutR
import Book2.Prop07.step13_dgquad
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.13 sub: the four figures AG, CF, DG, GE tile the whole square ADEB. Cut ADEB by the vertical
   CN (sum_parallelograms_area on a b d e AB DE AD BE, cut a-c-b / d-n-e) into left ADNC and right
   CNEB; then cut left ADNC by the horizontal HF (on a d c n AD CN AB DE, cut a-h-d / c-g-n) into
   AG and DG, and right CNEB by HF (on c n b e CN BE AB DE, cut c-g-n / b-f-e) into CF and GE. The
   three equations telescope to ADEB = △a:d:e + △a:e:b. -/
theorem helper_2_7_step13_tile (a b c d e n g h f : Point) (AB CN AD BE HF BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCN : c.onLine CN) (hgCN : g.onLine CN) (hnCN : n.onLine CN)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE) (hfBE : f.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hnDE : n.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHF : g.onLine HF) (hhHF : h.onLine HF) (hfHF : f.onLine HF)
    (hHFAB : ¬(HF.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCNAD : ¬(CN.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hade : ∠ a:d:e = ∟)
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟)
    (hbigpar : formParallelogram a b d e AB DE AD BE)
    (hparL : formParallelogram a d c n AD CN AB DE)
    (hparR : formParallelogram c n b e CN BE AB DE)
    (hparDG : formParallelogram h g d n HF DE AD CN)
    (hcgn : between c g n) (hdne : between d n e) (hahd : between a h d)
    (hbfe : between b f e) :
    (Triangle.area △ a:c:g + Triangle.area △ a:g:h)
      + (Triangle.area △ c:b:f + Triangle.area △ c:f:g)
      + (Triangle.area △ d:h:g + Triangle.area △ d:g:n)
      + (Triangle.area △ g:f:e + Triangle.area △ g:e:n) =
      Triangle.area △ a:d:e + Triangle.area △ a:e:b := by
  euclid_intros
  have step13_cut1 : Triangle.area △ a:d:n + Triangle.area △ a:n:c
      + (Triangle.area △ c:n:e + Triangle.area △ c:e:b)
      = Triangle.area △ a:d:e + Triangle.area △ a:e:b := by euclid_apply (helper_2_7_step13_cut1 a b c d e n AB DE AD BE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_cutL : Triangle.area △ a:c:g + Triangle.area △ a:g:h
      + (Triangle.area △ h:g:n + Triangle.area △ h:n:d)
      = Triangle.area △ a:c:n + Triangle.area △ a:n:d := by euclid_apply (helper_2_7_step13_cutL a d c n h g AD CN AB DE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_cutR : Triangle.area △ c:b:f + Triangle.area △ c:f:g
      + (Triangle.area △ g:f:e + Triangle.area △ g:e:n)
      = Triangle.area △ c:n:e + Triangle.area △ c:e:b := by euclid_apply (helper_2_7_step13_cutR c n b e g f CN BE AB DE (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step13_dgquad : Triangle.area △ d:h:g + Triangle.area △ d:g:n
      = Triangle.area △ h:g:n + Triangle.area △ h:n:d := by euclid_apply (helper_2_7_step13_dgquad h g d n HF DE AD CN (by assumption)); (try split_ands) <;> assumption
  euclid_finish

end Elements.Book2
