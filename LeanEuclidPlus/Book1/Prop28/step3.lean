import SystemE
import Book.Prop27
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_28_step3 (a b c d e f g h : Point) (AB CD EF : Line)
    (haonAB : a.onLine AB) (hbonAB : b.onLine AB) (hab : a ≠ b)
    (hconCD : c.onLine CD) (hdonCD : d.onLine CD) (hcd : c ≠ d)
    (heonEF : e.onLine EF) (hfonEF : f.onLine EF) (hef : e ≠ f)
    (hbet_ab : between a g b) (hbet_ch : between c h d)
    (hbet_eh : between e g h) (hbet_ghf : between g h f)
    (hstep1 : ∠ a:g:h = ∠ g:h:d)
    (hstep2 : a.opposingSides d EF) :
    ¬AB.intersectsLine CD := by
  have hgonAB : g.onLine AB := between_same_line_in a g b AB ⟨hbet_ab, haonAB, hbonAB⟩
  have honCD : h.onLine CD := between_same_line_in c h d CD ⟨hbet_ch, hconCD, hdonCD⟩
  have hgf : between e g f := between_trans_out e g h f ⟨hbet_eh, hbet_ghf⟩
  have hgonEF : g.onLine EF := between_same_line_in e g f EF ⟨hgf, heonEF, hfonEF⟩
  have hhonEF : h.onLine EF := between_same_line_out e g h EF ⟨hbet_eh, heonEF, hgonEF⟩
  have hdABag : distinctPointsOnLine a g AB := ⟨haonAB, hgonAB, by euclid_finish⟩
  have hdCDhd : distinctPointsOnLine h d CD := ⟨honCD, hdonCD, by euclid_finish⟩
  have hdEFgh : distinctPointsOnLine g h EF := ⟨hgonEF, hhonEF, by euclid_finish⟩
  euclid_apply (proposition_27 a d g h AB CD EF)
  euclid_finish

end Elements.Book1
