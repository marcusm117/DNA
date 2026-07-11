import SystemE
import Book1.Prop12.Main
import Book3.Prop14.step2_hfeq
import Book3.Prop14.step2_hgeq
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- 3.14.2: draw EF, EG from the centre E perpendicular to AB, CD [Prop 1.12].
-- We realize the I.12 construction (drop the perpendicular from E in the proof cone) and
-- identify its foot HF/HG with the given foot F/G by perpendicular-foot uniqueness,
-- using I.12's strengthened ∀-perpendicularity output.
theorem helper_3_14_step2
    (a b c d e f g : Point) (ABDC : Circle) (AB CD EF EG : Line)
    (ha : a.onCircle ABDC) (hb : b.onCircle ABDC)
    (hc : c.onCircle ABDC) (hd : d.onCircle ABDC)
    (hcen : e.isCentre ABDC)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hab_ne : a ≠ b)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hcd_ne : c ≠ d)
    (heEF : e.onLine EF) (hfEF : f.onLine EF) (hef : e ≠ f)
    (heEG : e.onLine EG) (hgEG : g.onLine EG) (heg : e ≠ g)
    (hfAB : f.onLine AB) (hgCD : g.onLine CD)
    (hafb : between a f b) (hcgd : between c g d)
    (hfangle : ∠ a:f:e = ∟) (hgangle : ∠ c:g:e = ∟) :
    distinctPointsOnLine e f EF ∧ distinctPointsOnLine e g EG
    ∧ ∠ a:f:e = ∟ ∧ ∠ c:g:e = ∟ := by
  have h_e_off_AB : ¬ e.onLine AB := by euclid_finish
  have h_e_off_CD : ¬ e.onLine CD := by euclid_finish
  euclid_apply (Elements.Book1.proposition_12 a b e AB)
  rename_i hf hhfAB hfdisj hperpf
  euclid_apply (Elements.Book1.proposition_12 c d e CD)
  rename_i hg hhgCD hgdisj hperpg
  have step2_hfeq : hf = f := by euclid_apply (helper_3_14_step2_hfeq a b e f hf AB (by euclid_assumption "" (show ¬ e.onLine AB; assumption)) (by euclid_assumption "" (show a.onLine AB; assumption)) (by euclid_assumption "" (show f.onLine AB; assumption)) (by euclid_assumption "" (show hf.onLine AB; assumption)) (by euclid_assumption "" (show between a f b; assumption)) (by euclid_assumption "" (show ∠ a:f:e = ∟; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine AB → p ≠ hf → ∠ p:hf:e = ∟; assumption)))
  have step2_hgeq : hg = g := by euclid_apply (helper_3_14_step2_hgeq c d e g hg CD (by euclid_assumption "" (show ¬ e.onLine CD; assumption)) (by euclid_assumption "" (show c.onLine CD; assumption)) (by euclid_assumption "" (show g.onLine CD; assumption)) (by euclid_assumption "" (show hg.onLine CD; assumption)) (by euclid_assumption "" (show between c g d; assumption)) (by euclid_assumption "" (show ∠ c:g:e = ∟; assumption)) (by euclid_assumption "" (show ∀ (p : Point), p.onLine CD → p ≠ hg → ∠ p:hg:e = ∟; assumption)))
  euclid_finish

end Elements.Book3
