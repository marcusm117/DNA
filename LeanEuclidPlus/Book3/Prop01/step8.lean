import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_1_step8 (g a d b : Point) (GA GD GB : Line)
    (h_g_GA : g.onLine GA) (h_a_GA : a.onLine GA)
    (h_g_GD : g.onLine GD) (h_d_GD : d.onLine GD)
    (h_g_GB : g.onLine GB) (h_b_GB : b.onLine GB)
    (h_gNa : g ≠ a) (h_gNd : g ≠ d) (h_gNb : g ≠ b) :
    distinctPointsOnLine g a GA ∧ distinctPointsOnLine g d GD ∧ distinctPointsOnLine g b GB :=
  ⟨⟨h_g_GA, h_a_GA, h_gNa⟩, ⟨h_g_GD, h_d_GD, h_gNd⟩, ⟨h_g_GB, h_b_GB, h_gNb⟩⟩

end Elements.Book3
