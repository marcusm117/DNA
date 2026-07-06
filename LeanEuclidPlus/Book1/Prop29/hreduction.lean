import SystemE
import Book1.Prop13.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_29_hreduction
    (a b c d e f g h : Point) (AB CD EF : Line)
    (ha_AB : a.onLine AB) (hb_AB : b.onLine AB) (hab : a ≠ b)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD) (hcd : c ≠ d)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF) (hef : e ≠ f)
    (hbetw_agb : between a g b) (hbetw_chd : between c h d)
    (hbetw_egh : between e g h) (hbetw_ghf : between g h f)
    (hside : b.sameSide d EF) (hpar : ¬AB.intersectsLine CD)
    (hne : ∠ a:g:h ≠ ∠ g:h:d)
    (hgt : ¬∠ a:g:h > ∠ g:h:d)
    (hstep1 : ∠ a:g:h ≠ ∠ g:h:d → ∠ a:g:h > ∠ g:h:d ∨ ∠ g:h:d > ∠ a:g:h) :
    False := by
  have hlt : ∠ g:h:d > ∠ a:g:h := by
    rcases hstep1 hne with h1 | h1
    · exact absurd h1 hgt
    · exact h1
  euclid_apply (proposition_13 g h c d EF CD)
  have hlt2 : ∠ a:g:h + ∠ c:h:g < ∟ + ∟ := by linarith
  euclid_finish

end Elements.Book1
