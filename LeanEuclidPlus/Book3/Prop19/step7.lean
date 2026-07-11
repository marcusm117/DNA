import SystemE
import Book1.Prop14.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- CF⊥DE and CA⊥DE at c → CA=CF (Prop.~1.14) → f.onLine CA. Contradiction.
theorem helper_3_19_step7
    (a c f e : Point) (CA DE CF : Line) (ABC : Circle)
    (h_caon_a : a.onLine CA)
    (h_caon_c : c.onLine CA)
    (h_anec : a ≠ c)
    (h_deon_c : c.onLine DE)
    (h_deon_e : e.onLine DE)
    (h_enec : e ≠ c)
    (h_cfon_f : f.onLine CF)
    (h_cfon_c : c.onLine CF)
    (h_centre : f.isCentre ABC)
    (h_no_int : ¬DE.intersectsCircle ABC)
    (step3 : ∠ f:c:e = ∟)
    (right_7 : ∠ a:c:e = ∟)
    (hsuppose1 : ¬f.onLine CA) : False := by
  have hfoff : ¬f.onLine DE := by
    intro hfon
    exact h_no_int (intersection_circle_line_2 f ABC DE
      ⟨center_inside_circle f ABC h_centre, hfon⟩)
  have h_fnec : f ≠ c := fun h => hfoff (h ▸ h_deon_c)
  have h_aoff : ¬a.onLine DE := by euclid_finish
  have h_dene_ca : DE ≠ CA := fun h => h_aoff (h ▸ h_caon_a)
  have h_eoff_ca : ¬e.onLine CA := by
    intro h
    exact h_dene_ca
      (two_points_determine_line c e CA DE
        ⟨⟨h_caon_c, h, h_enec.symm⟩, h_deon_c, h_deon_e⟩).symm
  have h_anec_rev : c ≠ a := h_anec.symm
  have h_ecf : ∠ e:c:f = ∟ := by euclid_apply (angle_symm f c e); linarith
  by_cases h_afDE : a.sameSide f DE
  · -- Same side: extend CA beyond c to a' opposing f.
    euclid_apply (extend_point CA a c) as a'
    have h_a'on_ca : a'.onLine CA := by euclid_finish
    have h_a'ne_c : a' ≠ c := by euclid_finish
    have h_a'off_de : ¬a'.onLine DE := by
      intro h
      exact h_dene_ca
        (two_points_determine_line c a' CA DE
          ⟨⟨h_caon_c, h_a'on_ca, h_a'ne_c.symm⟩, h_deon_c, h⟩).symm
    have h_a_a'_opp : ¬(a.sameSide a' DE) :=
      pasch_3 a c a' DE ⟨by euclid_finish, h_deon_c⟩
    have h_a'_not_ss_f : ¬(a'.sameSide f DE) := by
      intro h_a'f
      exact h_a_a'_opp (same_side_symm a' a DE
        (same_side_trans f a' a DE
          ⟨same_side_symm a' f DE h_a'f, same_side_symm a f DE h_afDE⟩))
    have h_eca' : ∠ e:c:a' = ∟ := by
      have hperp := perpendicular_onlyif a a' c e CA
        ⟨h_caon_a, h_a'on_ca, by euclid_finish, h_eoff_ca, right_7⟩
      linarith
    have h_ca_cf : CA = CF := Elements.Book1.proposition_14 e c a' f DE CA CF
      ⟨⟨h_deon_e, h_deon_c, h_enec⟩,
       ⟨h_caon_c, h_a'on_ca, h_a'ne_c.symm⟩,
       ⟨h_cfon_c, h_cfon_f, h_fnec.symm⟩,
       ⟨h_a'off_de, hfoff, h_a'_not_ss_f⟩,
       by linarith⟩
    exact hsuppose1 (h_ca_cf ▸ h_cfon_f)
  · -- Opposite sides: a.opposingSides f DE directly.
    have h_eca : ∠ e:c:a = ∟ := by euclid_apply (angle_symm a c e); linarith
    have h_ca_cf : CA = CF := Elements.Book1.proposition_14 e c a f DE CA CF
      ⟨⟨h_deon_e, h_deon_c, h_enec⟩,
       ⟨h_caon_c, h_caon_a, h_anec_rev⟩,
       ⟨h_cfon_c, h_cfon_f, h_fnec.symm⟩,
       ⟨h_aoff, hfoff, h_afDE⟩,
       by linarith⟩
    exact hsuppose1 (h_ca_cf ▸ h_cfon_f)

end Elements.Book3
