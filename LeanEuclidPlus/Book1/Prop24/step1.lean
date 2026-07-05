import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_24_step1
  (d e g g' g'' : Point) (DE DG : Line)
  (h_d_DE : d.onLine DE) (h_e_DE : e.onLine DE)
  (h_d_DG : d.onLine DG) (h_g'_DG : g'.onLine DG) (h_g''_DG : g''.onLine DG)
  (h_between_g' : between d g' g'') (h_between_g : between d g g'')
  (h_g'_ne_d : g' ≠ d) (h_de_ne : d ≠ e)
  (h_angle : ∠ g':d:e = ∠ b:a:c)
  (hassump1 : ∠ b:a:c > ∠ e:d:f)
  : ∠ e:d:g = ∠ b:a:c := by
  have h_g_DG : g.onLine DG := by euclid_finish
  have h_g_ne_d : g ≠ d := by euclid_finish
  have h_nbetween : ¬ between g d g' := by euclid_finish
  -- same-ray: ∠e:d:g = ∠e:d:g' since g, g' both on DG same side of d
  have h_same_ray : ∠ e:d:g = ∠ e:d:g' :=
    equal_angles d e e g g' DE DG
      ⟨h_d_DE, h_e_DE, h_e_DE, h_d_DG, h_g_DG, h_g'_DG,
       h_de_ne.symm, h_de_ne.symm, h_g_ne_d, h_g'_ne_d,
       by euclid_finish, h_nbetween⟩
  -- ∠g':d:e = ∠e:d:g' by angle_symm, then = ∠b:a:c
  have h_g'de_sym : ∠ e:d:g' = ∠ b:a:c :=
    (angle_symm g' d e ⟨h_g'_ne_d, h_de_ne⟩).symm.trans h_angle
  exact h_same_ray.trans h_g'de_sym

end Elements.Book1
