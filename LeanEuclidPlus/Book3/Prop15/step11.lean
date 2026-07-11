import SystemE
import Book1.Prop24.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11
    (e m n f g l k : Point)
    (ME MN EN FE FG EG : Line)
    (hm_ME : m.onLine ME) (he_ME : e.onLine ME)
    (hm_MN : m.onLine MN) (hn_MN : n.onLine MN) (hl_MN : l.onLine MN)
    (he_EN : e.onLine EN) (hn_EN : n.onLine EN)
    (hf_FE : f.onLine FE) (he_FE : e.onLine FE)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hk_FG : k.onLine FG)
    (he_EG : e.onLine EG) (hg_EG : g.onLine EG)
    (hbetw : between m l n)
    (hl_betw : between e l k)
    (hperp : ∠ m:l:e = ∟)
    (hperp_k : ∠ e:k:f = ∟)
    (hek : e ≠ k)
    (hk_ne_f : k ≠ f)
    (hfg : f ≠ g)
    (step11_assumption1 : |(m─e)| = |(f─e)| ∧ |(e─n)| = |(e─g)|)
    (step11_assumption2 : ∠ m:e:n > ∠ f:e:g) :
    |(m─n)| > |(f─g)| := by
  have h_tri_emn : formTriangle e m n ME MN EN := by euclid_finish
  have h_tri_efg : formTriangle e f g FE FG EG := by euclid_finish
  have h_em_ef : |(e─m)| = |(e─f)| := by
    linarith [step11_assumption1.1, segment_symmetric e m, segment_symmetric f e]
  have hconj24 : formTriangle e m n ME MN EN ∧ formTriangle e f g FE FG EG ∧
      |(e─m)| = |(e─f)| ∧ |(e─n)| = |(e─g)| ∧ ∠m:e:n > ∠f:e:g :=
    ⟨h_tri_emn, h_tri_efg, h_em_ef, step11_assumption1.2, step11_assumption2⟩
  euclid_apply (Elements.Book1.proposition_24 e m n e f g ME MN EN FE FG EG)
  euclid_finish

end Elements.Book3
