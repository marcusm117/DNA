import SystemE
import Book.Prop34
import Book2.Prop04.step5_cnad
import Book2.Prop04.step8_dnab
import Book2.Prop04.step9_anbe
import Book2.Prop04.step5_bgd
import Book2.Prop04.step9_par
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.17: ∠ c:g:k = ∟ and ∠ g:k:b = ∟. CGKB is a parallelogram (step9_par); its opposite angles are
   equal [Prop.~1.34]: ∠ c:g:k = ∠ c:b:k and ∠ g:k:b = ∠ b:c:g (proposition_34'). With ∠ k:b:c = ∟
   (step15, = ∠ c:b:k by symmetry) and ∠ b:c:g = ∟ (step16), both opposite angles are right. -/
theorem helper_2_4_step13_opp (a b c d e g k : Point) (AB CF AD BE HK BD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD))
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟)
    (hstep15 : ∠ k:b:c = ∟) (hstep16 : ∠ b:c:g = ∟) :
    ∠ c:g:k = ∟ ∧ ∠ g:k:b = ∟ := by
  euclid_intros
  -- off-line roots (same preamble as step9)
  have had : a ≠ d := by euclid_finish
  have step5_cnad : ¬(c.onLine AD) := by euclid_apply (helper_2_4_step5_cnad a b c d AB AD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step8_dnab : ¬(d.onLine AB) := by euclid_apply (helper_2_4_step8_dnab a b d AB (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have step9_anbe : ¬(a.onLine BE) := by euclid_apply (helper_2_4_step9_anbe a b e BE (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbd : b ≠ d := fun h => step8_dnab (h ▸ hbAB)
  have step5_bgd : between b g d := by euclid_apply (helper_2_4_step5_bgd a b c d g AB CF AD BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_par : formParallelogram c b g k AB HK CF BE := by euclid_apply (helper_2_4_step9_par a b c d e g k AB CF AD BE HK BD (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)); (try split_ands) <;> assumption
  euclid_apply (proposition_34' c b g k AB HK CF BE)
  euclid_finish

end Elements.Book2
