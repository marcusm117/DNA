import SystemE
import Book3.Prop03.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step11_assumption2_bisect
    (m n e l k m0 : Point) (ABCD : Circle) (MN EK : Line)
    (h_centre : e.isCentre ABCD)
    (hm_on : m.onCircle ABCD) (hn_on : n.onCircle ABCD)
    (he_EK : e.onLine EK) (hk_EK : k.onLine EK)
    (hm_MN : m.onLine MN) (hn_MN : n.onLine MN) (hl_MN : l.onLine MN)
    (hm0_MN : m0.onLine MN) (hm0_off : ¬m0.onLine EK)
    (hl_betw : between e l k)
    (hbetw : between m l n)
    (hperp : ∠ m:l:e = ∟) :
    |(m─l)| = |(l─n)| := by
  -- l is on EK (from between e l k)
  have h_l_EK : l.onLine EK := between_same_line_in e l k EK ⟨hl_betw, he_EK, hk_EK⟩
  -- e ≠ l
  have h_e_ne_l : e ≠ l := (between_symm e l k hl_betw).2.1
  -- ¬e.onLine MN
  have h_e_off_MN : ¬e.onLine MN := by
    intro h_e_on_MN
    have h_EK_MN : EK = MN := two_points_determine_line e l EK MN
      ⟨⟨he_EK, h_l_EK, h_e_ne_l⟩, h_e_on_MN, hl_MN⟩
    rw [← h_EK_MN] at hm0_MN
    exact hm0_off hm0_MN
  -- m ≠ n
  have h_m_ne_n : m ≠ n := (between_symm m l n hbetw).2.2.1
  -- Apply proposition_3: ⊥→bisect direction
  exact (proposition_3 m n e l ABCD MN EK
    ⟨hm_on, hn_on, ⟨hm_MN, hn_MN, h_m_ne_n⟩, h_centre, he_EK, h_e_off_MN,
     hl_MN, h_l_EK, hbetw⟩).2 hperp

end Elements.Book3
