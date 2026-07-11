import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step1 (a f g : Point) (ABC : Circle)
    (hg_in_ABC : g.insideCircle ABC)
    (hfg : f ≠ g)
    (ha_ABC : a.onCircle ABC)
    (hsuppose1 : ¬between f g a)
    : ∃ h : Point, h ≠ a ∧ h.onCircle ABC ∧ between f g h := by
  euclid_apply (line_from_points f g) as FG
  have hg_FG : g.onLine FG := by euclid_finish
  have hf_FG : f.onLine FG := by euclid_finish
  have hdist : distinctPointsOnLine g f FG := ⟨hg_FG, hf_FG, fun h => hfg h.symm⟩
  -- extending past g from f gives a point on ABC beyond g
  obtain ⟨h, hh_ABC, hh_FG, hbet_hgf⟩ :=
    intersection_circle_line_extending_points ABC FG g f ⟨hg_in_ABC, hdist⟩
  -- between h g f → between f g h
  have hbet_fgh : between f g h := (between_symm h g f hbet_hgf).1
  -- h ≠ a: if h = a then between f g a, contradicting hsuppose1
  have hne : h ≠ a := by
    intro heq
    subst heq
    exact hsuppose1 hbet_fgh
  exact ⟨h, hne, hh_ABC, hbet_fgh⟩

end Elements.Book3
