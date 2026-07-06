import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_46_step13
    (a b c d c1 : Point) (AB AC AD : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hc1_AC : c1.onLine AC)
    (hbet_acc1 : between a c c1) (hbet_adc1 : between a d c1)
    (hc_off_AB : ¬c.onLine AB)
    (ha_AD : a.onLine AD) (hd_AD : d.onLine AD)
    (step1 : ∠ c:a:b = ∟) :
    ∠ b:a:d = ∟ := by
  have hd_AC : d.onLine AC := between_same_line_in a d c1 AC ⟨hbet_adc1, ha_AC, hc1_AC⟩
  have had_ne : a ≠ d := by euclid_finish
  have hAC_eq_AD : AC = AD :=
    two_points_determine_line a d AC AD ⟨⟨ha_AC, hd_AC, had_ne⟩, ha_AD, hd_AD⟩
  have hc_ne_a : c ≠ a := fun h => hc_off_AB (h ▸ ha_AB)
  have hno_bet_cad : ¬(between c a d) := by euclid_finish
  have hno_bet_bab : ¬(between b a b) := by euclid_finish
  have h_eq := equal_angles a c d b b AC AB
    ⟨ha_AC, hc_AC, hd_AC, ha_AB, hb_AB, hb_AB, hc_ne_a, had_ne.symm, hab.symm, hab.symm,
     hno_bet_cad, hno_bet_bab⟩
  euclid_finish

end Elements.Book1
