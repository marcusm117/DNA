import SystemE
import Book3.Prop36.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_37_step5 (a c d e : Point) (ABC : Circle) (DE : Line)
  (h_a : a.onCircle ABC) (h_c : c.onCircle ABC) (h_bet : between d c a)
  (h_d_nins : ¬ d.insideCircle ABC) (h_d_noc : ¬ d.onCircle ABC)
  (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE) (h_e : e.onCircle ABC)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : (∃ p : Point, p.onLine DE ∧ p.onCircle ABC) ∧ ¬ DE.intersectsCircle ABC)   -- "$DE$ touches circle $ABC$"
  (hassump2 : ∃ DCA : Line, d.onLine DCA ∧ c.onLine DCA ∧ a.onLine DCA ∧ DCA.intersectsCircle ABC)   -- "$DCA$ cuts (it)"
  : |(a─d)| * |(d─c)| = |(d─e)| * |(d─e)| := by
  obtain ⟨_, h_nint⟩ := hassump1
  euclid_apply (proposition_36 a e c d ABC DE)
  euclid_finish

end Elements.Book3
