import SystemE
import Book2.Prop07.step3_bnhf
import Book2.Prop07.step3_dnhf
import Book2.Prop07.step3_ande
import Book2.Prop07.step3_dehf
import Book2.Prop07.step3_dse
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.7.3 sub: f (= HF ∩ BE) is between b and e on the right side BE. HF separates b from e:
   • along the diagonal BD, g (∈ HF) is between b and d (step3_bgd), so b and d are on opposite
     sides of HF (pasch_3);
   • d and e both lie on DE ∥ HF (step3_dehf), so d and e are on the same side of HF (step3_dse);
   hence b and e are on opposite sides of HF, and the crossing point f of BE with HF lies between
   them (pasch_4). -/
theorem helper_2_7_step3_bke (a b d e g f : Point) (BE HF DE BD AB CN AD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hfBE : f.onLine BE)
    (hgHF : g.onLine HF) (hfHF : f.onLine HF)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hHFAB : ¬(HF.intersectsLine AB)) (hDEAB : ¬(DE.intersectsLine AB))
    (hbgd : between b g d) (hde : d ≠ e)
    (hgnAB : ¬(g.onLine AB)) (hdnAB : ¬(d.onLine AB)) :
    between b f e := by
  euclid_intros
  have hdg : d ≠ g := by euclid_finish
  have hgd : g ≠ d := fun h => hdg h.symm
  have step3_bnhf : ¬(b.onLine HF) := by euclid_apply (helper_2_7_step3_bnhf b g AB HF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_dnhf : ¬(d.onLine HF) := by euclid_apply (helper_2_7_step3_dnhf b d g BD HF (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step3_ande : ¬(a.onLine DE) := by euclid_apply (helper_2_7_step3_ande a d AB DE (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hDEHF : DE ≠ HF := fun h => step3_dnhf (h ▸ hdDE)
  have hHFAB' : HF ≠ AB := fun h => hgnAB (h ▸ hgHF)
  have hABDE : AB ≠ DE := fun h => step3_ande (h ▸ haAB)
  have hbf : b ≠ f := fun h => step3_bnhf (h ▸ hfHF)
  have step3_dehf : ¬(DE.intersectsLine HF) := by euclid_apply (helper_2_7_step3_dehf DE HF AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have henhf : ¬(e.onLine HF) := by
    intro hon; euclid_apply (intersection_lines_common_point e DE HF); euclid_finish
  have hef : e ≠ f := fun h => henhf (h ▸ hfHF)
  have step3_dse : d.sameSide e HF := by euclid_apply (helper_2_7_step3_dse d e DE HF (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_apply (pasch_3 b g d HF)
  euclid_apply (pasch_4 b f e HF BE)
  euclid_finish

end Elements.Book2
