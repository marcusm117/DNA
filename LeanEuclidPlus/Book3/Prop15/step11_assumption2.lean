import SystemE
import Mathlib.Tactic.Linarith
import Book1.Prop25.Main
import Book3.Prop15.step11_assumption2_bisect
import Book3.Prop15.step11_assumption2_pm
import Book3.Prop15.step11_assumption2_pf
import Book3.Prop15.step11_assumption2_e_off_fg
import Book3.Prop15.step11_assumption2_fkg
import Book3.Prop15.step11_assumption2_pg
import Book3.Prop15.step11_assumption2_fg_le
import Book3.Prop15.step11_assumption2_arith
import Book3.Prop15.step11_assumption2_e_off_mn
import Book3.Prop15.step11_assumption2_tri_emn
import Book3.Prop15.step11_assumption2_tri_efg
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

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
    (right_12 : f ≠ g)
    (hk_ne_f : k ≠ f) :
    ∠ m:e:n > ∠ f:e:g := by
  -- All heavy sub-computations delegated to backing files
  have step11_assumption2_bisect : |(m─l)| = |(l─n)| := by euclid_apply (helper_3_15_step11_assumption2_bisect m n e l k m0 ABCD MN EK (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show n.onCircle ABCD; assumption)) (by euclid_assumption "" (show e.onLine EK; assumption)) (by euclid_assumption "" (show k.onLine EK; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show l.onLine MN; assumption)) (by euclid_assumption "" (show m0.onLine MN; assumption)) (by euclid_assumption "" (show ¬m0.onLine EK; assumption)) (by euclid_assumption "" (show between e l k; assumption)) (by euclid_assumption "" (show between m l n; assumption)) (by euclid_assumption "" (show ∠ m:l:e = ∟; assumption)))
  have step11_assumption2_pm : |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)| := by euclid_apply (helper_3_15_step11_assumption2_pm m l e ABCD MN (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show l.onLine MN; assumption)) (by euclid_assumption "" (show ∠ m:l:e = ∟; assumption)))
  have step11_assumption2_pf : |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)| := by euclid_apply (helper_3_15_step11_assumption2_pf k f e ABCD FG (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show f.onCircle ABCD; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine FG; assumption)) (by euclid_assumption "" (show ∠ e:k:f = ∟; assumption)))
  -- k ≠ e: from between e l k (hl_betw), via between_symm
  have hk_ne_e : k ≠ e := (between_symm e l k hl_betw).2.2.1.symm
  have step11_assumption2_e_off_fg : ¬e.onLine FG := by euclid_apply (helper_3_15_step11_assumption2_e_off_fg e f k FG (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine FG; assumption)) (by euclid_assumption "" (show ∠ e:k:f = ∟; assumption)) (by euclid_assumption "" (show k ≠ e; assumption)) (by euclid_assumption "" (show k ≠ f; assumption)))
  -- @euclid_gap: Euclid reads foot k of perpendicular between chord endpoints f and g off the figure;
  -- System-E's proposition_3 requires between f k g as INPUT, not conclusion, so it cannot be derived
  -- from the available hypotheses without giving it here
  have step11_assumption2_fkg : between f k g := by euclid_apply (helper_3_15_step11_assumption2_fkg f k g e ABCD FG (by euclid_assumption "" (show f.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine FG; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show k ≠ f; assumption)) (by euclid_assumption "" (show |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)|; assumption)))
  have step11_assumption2_pg : |(k─g)| * |(k─g)| + |(e─k)| * |(e─k)| = |(e─g)| * |(e─g)| := by euclid_apply (helper_3_15_step11_assumption2_pg k g e f ABCD FG EK (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine FG; assumption)) (by euclid_assumption "" (show e.onLine EK; assumption)) (by euclid_assumption "" (show k.onLine EK; assumption)) (by euclid_assumption "" (show ¬e.onLine FG; assumption)) (by euclid_assumption "" (show ∠ e:k:f = ∟; assumption)) (by euclid_assumption "" (show between f k g; assumption)))
  have step11_assumption2_fg_le : |(f─g)| ≤ |(k─f)| + |(k─f)| := by euclid_apply (helper_3_15_step11_assumption2_fg_le f g k e ABCD FG (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show f.onCircle ABCD; assumption)) (by euclid_assumption "" (show g.onCircle ABCD; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show k.onLine FG; assumption)) (by euclid_assumption "" (show |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)|; assumption)) (by euclid_assumption "" (show |(k─g)| * |(k─g)| + |(e─k)| * |(e─k)| = |(e─g)| * |(e─g)|; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)))
  have step11_assumption2_arith : |(m─n)| > |(f─g)| := by euclid_apply (helper_3_15_step11_assumption2_arith l m n e k f g h (by euclid_assumption "" (show |(m─l)| = |(l─n)|; assumption)) (by euclid_assumption "" (show between m l n; assumption)) (by euclid_assumption "" (show |(l─m)| * |(l─m)| + |(e─l)| * |(e─l)| = |(e─m)| * |(e─m)|; assumption)) (by euclid_assumption "" (show |(k─f)| * |(k─f)| + |(e─k)| * |(e─k)| = |(e─f)| * |(e─f)|; assumption)) (by euclid_assumption "" (show |(m─e)| = |(f─e)| ∧ |(e─n)| = |(e─g)|; assumption)) (by euclid_assumption "" (show |(e─h)| < |(e─k)|; assumption)) (by euclid_assumption "" (show |(e─l)| = |(e─h)|; assumption)) (by euclid_assumption "" (show |(f─g)| ≤ |(k─f)| + |(k─f)|; assumption)))
  -- Derived facts needed for tri_emn SP suppliability
  have h_m_ne_n : m ≠ n := (between_symm m l n hbetw).2.2.1
  have step11_assumption2_e_off_mn : ¬e.onLine MN := by euclid_apply (helper_3_15_step11_assumption2_e_off_mn e l k m0 EK MN (by euclid_assumption "" (show e.onLine EK; assumption)) (by euclid_assumption "" (show k.onLine EK; assumption)) (by euclid_assumption "" (show l.onLine MN; assumption)) (by euclid_assumption "" (show m0.onLine MN; assumption)) (by euclid_assumption "" (show ¬m0.onLine EK; assumption)) (by euclid_assumption "" (show between e l k; assumption)))
  have step11_assumption2_tri_emn : formTriangle e m n ME MN EN := by euclid_apply (helper_3_15_step11_assumption2_tri_emn e m n ABCD ME MN EN (by euclid_assumption "" (show e.isCentre ABCD; assumption)) (by euclid_assumption "" (show m.onCircle ABCD; assumption)) (by euclid_assumption "" (show n.onCircle ABCD; assumption)) (by euclid_assumption "" (show m.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine ME; assumption)) (by euclid_assumption "" (show e.onLine EN; assumption)) (by euclid_assumption "" (show n.onLine EN; assumption)) (by euclid_assumption "" (show m.onLine MN; assumption)) (by euclid_assumption "" (show n.onLine MN; assumption)) (by euclid_assumption "" (show m ≠ n; assumption)) (by euclid_assumption "" (show ¬e.onLine MN; assumption)))
  have step11_assumption2_tri_efg : formTriangle e f g FE FG EG := by euclid_apply (helper_3_15_step11_assumption2_tri_efg e f g FE FG EG (by euclid_assumption "" (show f.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine FE; assumption)) (by euclid_assumption "" (show e.onLine EG; assumption)) (by euclid_assumption "" (show g.onLine EG; assumption)) (by euclid_assumption "" (show f.onLine FG; assumption)) (by euclid_assumption "" (show g.onLine FG; assumption)) (by euclid_assumption "" (show f ≠ g; assumption)) (by euclid_assumption "" (show ¬e.onLine FG; assumption)))
  -- Equal radii (trivial linarith from step11_assumption1 + segment_symmetric)
  have h_em_ef : |(e─m)| = |(e─f)| := by
    linarith [step11_assumption1.1, segment_symmetric e m, segment_symmetric f e]
  -- Conclude via proposition_25
  exact Elements.Book1.proposition_25 e m n e f g ME MN EN FE FG EG
    ⟨step11_assumption2_tri_emn, step11_assumption2_tri_efg,
     h_em_ef, step11_assumption1.2, step11_assumption2_arith⟩

end Elements.Book3
