import SystemE
import Book1.Prop20.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- w' is the ABDC point on GH past g (between w' g h): |h-w'| = |g-w'| + |gh| = |g-p| + |gh| (p on ABDC).
-- In triangle g·h·p (non-degenerate since p is off GH), I.20 gives |h-g| + |g-p| > |h-p| = r_EBFD
-- (p on EBFD), so |h-w'| > r_EBFD, i.e. w' is outside EBFD. Used with p = whichever of d,b is off GH.
theorem helper_3_13_step4_int_wout (ABDC EBFD : Circle) (p g h w' : Point) (GH : Line)
    (hp_ABDC : p.onCircle ABDC) (hp_EBFD : p.onCircle EBFD)
    (hcenABDC : g.isCentre ABDC) (hcenEBFD : h.isCentre EBFD)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h)
    (hw'_ABDC : w'.onCircle ABDC) (hw'_GH : w'.onLine GH) (hw'_bet : between w' g h)
    (hp_off : ¬p.onLine GH) :
    w'.outsideCircle EBFD := by
  have hgp : g ≠ p := fun he => hp_off (he ▸ hgGH)
  have hhp : h ≠ p := fun he => hp_off (he ▸ hhGH)
  euclid_apply (line_from_points g p) as GP
  euclid_apply (line_from_points h p) as HP
  euclid_apply (Elements.Book1.proposition_20 g h p GH HP GP)
  euclid_finish

end Elements.Book3
