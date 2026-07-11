import SystemE
import Book1.Prop12.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_step1
    (e h k b c f g : Point) (EH EK BC FG : Line)
    (hEH : distinctPointsOnLine e h EH)
    (hEK : distinctPointsOnLine e k EK)
    (hb_BC : b.onLine BC)
    (hc_BC : c.onLine BC)
    (hbc_ne : b ≠ c)
    (hh_BC : h.onLine BC)
    (h_ang_h : ∠ e:h:b = ∟)
    (h_ang_k : ∠ e:k:f = ∟)
    (heh : e ≠ h)
    (hkf : k ≠ f)
    (hhb : h ≠ b) :
    distinctPointsOnLine e h EH ∧ distinctPointsOnLine e k EK ∧ ∠ e:h:b = ∟ ∧ ∠ e:k:f = ∟ := by
  have he_EH : e.onLine EH := by euclid_finish
  have hh_EH : h.onLine EH := by euclid_finish
  have he_off : ¬e.onLine BC := by
    intro h_on
    have hEH_BC : EH = BC := two_points_determine_line e h EH BC ⟨hEH, h_on, hh_BC⟩
    have hb_EH : b.onLine EH := by rw [hEH_BC]; exact hb_BC
    by_cases hbetw : between b h e
    · linarith [flat_angle_onlyif e h b (between_symm b h e hbetw).1, right_angle_pos]
    · linarith [degenerated_angle_if h b e EH ⟨hhb, heh.symm, hh_EH, hb_EH, he_EH, hbetw⟩,
                angle_symm e h b ⟨heh, hhb⟩, right_angle_pos]
  -- Criterion-3 citation for [Prop.~1.12]: drop perpendicular from e to BC.
  have h_prop12_cite : ∠ e:h:b = ∟ := by
    euclid_apply (Elements.Book1.proposition_12 b c e BC)
    euclid_finish
  exact ⟨hEH, hEK, h_ang_h, h_ang_k⟩

end Elements.Book3
