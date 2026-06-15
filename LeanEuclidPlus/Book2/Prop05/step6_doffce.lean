import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: d ∉ CE. c, d are distinct on AB (c ≠ d from between a c d). If d ∈ CE then c, d are two
   distinct points on both CE and AB, forcing CE = AB (two_points_determine_line), putting e ∈ AB —
   contradicting step6_big_eoff (the ∠b:c:e degeneracy). (Mirror of Prop06 step7_coffdf shape.) -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step6_doffce (a b c d e : Point) (AB CE : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (hacd : between a c d) (hcdb : between c d b)
    (hcelen : |(c─e)| = |(c─b)|) (hbce : ∠ b:c:e = ∟) :
    ¬(d.onLine CE) := by
  have step6_big_eoff : ¬(e.onLine AB) := by sorry
  intro hdCE
  euclid_apply (two_points_determine_line c d CE AB)
  euclid_finish

end Elements.Book2
