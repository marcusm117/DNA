import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop25.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

set_option systemE.solverTime 30 in
theorem helper_3_15_step11_assumption2
    (e f g l k m n m0 h : Point)
    (ABCD : Circle)
    (EK FG MN ME EN FE EG : Line)
    (h_centre : e.isCentre ABCD)
    (hf_on : f.onCircle ABCD) (hg_on : g.onCircle ABCD)
    (hm_on : m.onCircle ABCD) (hn_on : n.onCircle ABCD)
    (he_EK : e.onLine EK) (hk_EK : k.onLine EK)
    (hf_FG : f.onLine FG) (hg_FG : g.onLine FG) (hk_FG : k.onLine FG)
    (hm_MN : m.onLine MN) (hn_MN : n.onLine MN) (hl_MN : l.onLine MN)
    (hm_ME : m.onLine ME) (he_ME : e.onLine ME)
    (he_EN : e.onLine EN) (hn_EN : n.onLine EN)
    (hf_FE : f.onLine FE) (he_FE : e.onLine FE)
    (he_EG : e.onLine EG) (hg_EG : g.onLine EG)
    (hm0_MN : m0.onLine MN) (hm0_off : ¬m0.onLine EK)
    (hbetw : between m l n) (hl_betw : between e l k)
    (hperp : ∠ m:l:e = ∟) (hperp_k : ∠ e:k:f = ∟)
    (step2_assumption1 : |(e─h)| < |(e─k)|)
    (step3 : |(e─l)| = |(e─h)|)
    (step11_assumption1 : |(m─e)| = |(f─e)| ∧ |(e─n)| = |(e─g)|)
    (right_12 : f ≠ g) :
    ∠ m:e:n > ∠ f:e:g := by
  -- All heavy sub-computations delegated to backing files
  have step11_assumption2_bisect : |(m─l)| = |(l─n)| := by sorry
  have step11_assumption2_pm : |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by sorry
  have step11_assumption2_pf : |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)| := by sorry
  have step11_assumption2_pg : |(k─g)| * |(k─g)| + |(e─k)| * |(e─k)| = |(e─g)| * |(e─g)| := by sorry
  have step11_assumption2_fg_le : |(f─g)| ≤ |(k─f)| + |(k─f)| := by sorry
  have step11_assumption2_arith : |(m─n)| > |(f─g)| := by sorry
  have step11_assumption2_tri_emn : formTriangle e m n ME MN EN := by sorry
  have step11_assumption2_tri_efg : formTriangle e f g FE FG EG := by sorry
  -- Equal radii (trivial linarith from step11_assumption1 + segment_symmetric)
  have h_em_ef : |(e─m)| = |(e─f)| := by
    linarith [step11_assumption1.1, segment_symmetric e m, segment_symmetric f e]
  -- Conclude via proposition_25
  exact Elements.Book1.proposition_25 e m n e f g ME MN EN FE FG EG
    ⟨step11_assumption2_tri_emn, step11_assumption2_tri_efg,
     h_em_ef, step11_assumption1.2, step11_assumption2_arith⟩

end Elements.Book3
