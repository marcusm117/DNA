import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.5 sub-sub: a and d are on the same side of CF. Both lie on AD, which does not cross CF.
   c distinguishes the lines: c ∈ CF, but c ∉ AD — c is strictly between a and b on AB (so c ≠ a),
   and AD meets AB only at a (∠ b:a:d = ∟ ⟹ AD ≠ AB), so c ∉ AD. Hence CF ≠ AD; then a, d are off
   CF (a shared point of two distinct lines makes them intersect); finally a, d off CF on a line
   parallel to CF lie on the same side. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step5_bgd_ss (a b c d : Point) (AB CF AD : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD)
    (hab : a ≠ b) (had : a ≠ d)
    (hbad : ∠ b:a:d = ∟)
    (hCFAD : ¬(CF.intersectsLine AD)) :
    a.sameSide d CF := by
  euclid_intros
  have step5_cnad : ¬(c.onLine AD) := by sorry
  have hne : CF ≠ AD := by
    intro heq; rw [heq] at hcCF; exact step5_cnad hcCF
  have haoff : ¬(a.onLine CF) := by
    intro hon
    euclid_apply (intersection_lines_common_point a CF AD)
    euclid_finish
  have hdoff : ¬(d.onLine CF) := by
    intro hon
    euclid_apply (intersection_lines_common_point d CF AD)
    euclid_finish
  by_contra hcon
  euclid_apply (intersection_lines_opposing a d CF AD)
  euclid_apply (intersection_symm CF AD)
  euclid_finish

end Elements.Book2
