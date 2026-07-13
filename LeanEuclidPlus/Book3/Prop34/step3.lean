import SystemE
import Book3.Prop32.Main
import Book3.Prop34.step3_w
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_34_step3 (a b c e f : Point) (ABC : Circle) (EF BC : Line)
  (he_EF : e.onLine EF) (hf_EF : f.onLine EF) (hbet_ebf : between e b f)
  (ha_ABC : a.onCircle ABC) (ha_opp : a.opposingSides f BC)
  (hBC_int : BC.intersectsCircle ABC)
  -- Reasoning hypotheses (from @assumption — keep these types in the signature):
  (hassump1 : b.onLine EF ∧ b.onCircle ABC ∧ ¬ EF.intersectsCircle ABC)   -- "some straight-line $EF$ touches the circle $ABC$"
  (hassump2 : b.onCircle ABC ∧ b.onLine BC ∧ c.onCircle ABC ∧ c.onLine BC ∧ b ≠ c)   -- "$BC$ has been drawn across (the circle) from the point of contact $B$"
  : ∠ f:b:c = ∠ b:a:c := by
  obtain ⟨hb_EF, hb_ABC, hEF_notint⟩ := hassump1
  obtain ⟨_, hb_BC, hc_ABC, hc_BC, hbc_ne⟩ := hassump2
  -- witness w in the alternate segment on the e-side of BC (mirror of a)
  have step3_w : ∃ w : Point, w.onCircle ABC ∧ w.opposingSides e BC := by euclid_apply (helper_3_34_step3_w b c e f ABC BC EF (by euclid_assumption "" (show b.onCircle ABC; assumption)) (by euclid_assumption "" (show c.onCircle ABC; assumption)) (by euclid_assumption "" (show b.onLine BC; assumption)) (by euclid_assumption "" (show c.onLine BC; assumption)) (by euclid_assumption "" (show b ≠ c; assumption)) (by euclid_assumption "" (show e.onLine EF; assumption)) (by euclid_assumption "" (show b.onLine EF; assumption)) (by euclid_assumption "" (show between e b f; assumption)) (by euclid_assumption "" (show BC.intersectsCircle ABC; assumption)) (by euclid_assumption "" (show ¬ EF.intersectsCircle ABC; assumption)))
  obtain ⟨w, hw_ABC, hw_opp⟩ := step3_w
  -- III.32 alternate-segment theorem (Euclid III.32 = proposition_32)
  euclid_apply (proposition_32 b a c w e f ABC EF BC)
  euclid_finish

end Elements.Book3
