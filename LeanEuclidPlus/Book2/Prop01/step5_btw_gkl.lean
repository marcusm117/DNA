import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- Helper for 2.1.5: the foot k of DK on GH lies between the feet g (of BF) and l (of EL).
   k ∈ DK ∩ GH; g and l are distinct points of GH. g and l are on OPPOSITE sides of DK:
   g shares b's side (b.sameSide g DK), l shares e's side (e.sameSide l DK), and b,e are on
   opposite sides of DK because d (between b and e on BC) lies on DK (pasch_3). Then pasch_4
   on g, k, l across DK and GH gives between g k l. -/
theorem helper_2_1_step5_btw_gkl (b d e g k l : Point) (BC GH DK : Line)
    (hbBC : b.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e)
    (hgGH : g.onLine GH) (hkGH : k.onLine GH) (hlGH : l.onLine GH)
    (hdDK : d.onLine DK) (hkDK : k.onLine DK)
    (hssbg : b.sameSide g DK) (hssel : e.sameSide l DK) :
    between g k l := by
  euclid_intros
  euclid_apply (pasch_3 b d e DK)
  euclid_apply (pasch_4 g k l DK GH)
  euclid_finish

end Elements.Book2
