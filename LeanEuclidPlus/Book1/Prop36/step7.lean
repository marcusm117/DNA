import SystemE
import Book1.Prop35.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_36_step7 (a b c d e h : Point) (AH BG AB CD BE CH : Line)
  (h_a_AH : a.onLine AH) (h_d_AH : d.onLine AH)
  (h_b_BG : b.onLine BG) (h_c_BG : c.onLine BG)
  (h_a_AB : a.onLine AB) (h_b_AB : b.onLine AB)
  (h_d_CD : d.onLine CD) (h_c_CD : c.onLine CD) (h_d_ne_c : d ≠ c)
  (h_ss_ab_CD : a.sameSide b CD)
  (h_ab_ne_cd : ¬AB.intersectsLine CD)
  (h_par : ¬AH.intersectsLine BG)
  (h_step6 : formParallelogram e h b c AH BG BE CH)
  (hassump1 : distinctPointsOnLine b c BG)
  (hassump2 : ¬(BG.intersectsLine AH)) :
  Triangle.area △ e:b:h + Triangle.area △ c:b:h = Triangle.area △ a:b:d + Triangle.area △ d:b:c := by
  have h_pgram1 : formParallelogram a d b c AH BG AB CD :=
    ⟨h_a_AH, h_d_AH, h_b_BG, h_c_BG, h_a_AB, h_b_AB,
     ⟨h_d_CD, h_c_CD, h_d_ne_c⟩, h_ss_ab_CD, h_par, h_ab_ne_cd⟩
  euclid_apply (proposition_35' a b c d e h AH BG AB CD BE CH)
  euclid_finish

end Elements.Book1
