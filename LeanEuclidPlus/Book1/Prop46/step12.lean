import SystemE
import Helpers.SameSide
import Book.Prop29
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1
open Elements

theorem helper_1_46_step12
    (a b c d e c1 : Point)
    (AB AC AD BE DE : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (ha_AC : a.onLine AC) (hc_AC : c.onLine AC)
    (hc1_AC : c1.onLine AC) (hbet : between a d c1)
    (hc_off_AB : ¬c.onLine AB)
    (ha_AD : a.onLine AD) (hd_AD : d.onLine AD)
    (hd_DE : d.onLine DE) (he_DE : e.onLine DE)
    (hb_BE : b.onLine BE) (he_BE : e.onLine BE)
    (step3_par : ¬(DE.intersectsLine AB))
    (step4_par : ¬(BE.intersectsLine AD))
    (step6 : |(a─b)| = |(d─e)|) :
    ∠ b:a:d + ∠ a:d:e = ∟ + ∟ := by
  have had_ne : a ≠ d := by euclid_finish
  have hde_ne : d ≠ e := by euclid_finish
  have hd_AC : d.onLine AC := between_same_line_in a d c1 AC ⟨hbet, ha_AC, hc1_AC⟩
  have hAC_eq_AD : AC = AD :=
    two_points_determine_line a d AC AD ⟨⟨ha_AC, hd_AC, had_ne⟩, ha_AD, hd_AD⟩
  have hpar_AD_BE : ¬AD.intersectsLine BE :=
    fun h => step4_par (intersection_symm AD BE h)
  have hBE_ne_AD : BE ≠ AD := by
    intro h
    have hb_on_AD : b.onLine AD := h ▸ hb_BE
    have hAB_eq_AD : AB = AD :=
      two_points_determine_line a b AB AD ⟨⟨ha_AB, hb_AB, hab⟩, ha_AD, hb_on_AD⟩
    exact hc_off_AB (hAB_eq_AD ▸ (hAC_eq_AD ▸ hc_AC))
  have ha_off_BE : ¬a.onLine BE := fun h =>
    hpar_AD_BE (intersection_symm BE AD (intersection_lines_common_point a BE AD ⟨h, ha_AD, hBE_ne_AD⟩))
  have hss : b.sameSide e AD :=
    sameSide_of_parallel b e a BE AD hb_BE he_BE ha_AD ha_off_BE hpar_AD_BE
  have hAB_not_int_DE : ¬(AB.intersectsLine DE) :=
    fun h => step3_par (intersection_symm AB DE h)
  euclid_apply (proposition_29''''' b e a d AB DE AD
    ⟨⟨ha_AB, hb_AB, hab⟩, ⟨hd_DE, he_DE, hde_ne⟩, ⟨ha_AD, hd_AD, had_ne⟩, hss, hAB_not_int_DE⟩)

end Elements.Book1
