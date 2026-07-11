import SystemE
import Book3.Prop13.step4_int_nboth
import Book3.Prop13.step4_int_wout
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Two distinct common points d, b of ABDC, EBFD force the circles to intersect. The midpoint m of chord
-- db is inside BOTH circles; w' (the ABDC point on GH past g) is OUTSIDE EBFD (via I.20 on the
-- non-degenerate triangle g·h·p, p = whichever of d,b is off GH — at least one is, else g = h). Then
-- intersection_circle_circle_1 with m inside EBFD and w' outside EBFD (both on/inside ABDC) gives
-- ABDC.intersectsCircle EBFD. Independent of whether h is inside or outside ABDC (both touch cases).
theorem helper_3_13_step4_int (ABDC EBFD : Circle) (d b g h : Point) (GH : Line)
    (hd_ABDC : d.onCircle ABDC) (hd_EBFD : d.onCircle EBFD)
    (hb_ABDC : b.onCircle ABDC) (hb_EBFD : b.onCircle EBFD)
    (hdb : d ≠ b)
    (hne : ABDC ≠ EBFD)
    (hcenABDC : g.isCentre ABDC) (hcenEBFD : h.isCentre EBFD)
    (hgGH : g.onLine GH) (hhGH : h.onLine GH) (hgh : g ≠ h) :
    ABDC.intersectsCircle EBFD := by
  have step4_int_nboth : ¬(d.onLine GH ∧ b.onLine GH) := by euclid_apply (helper_3_13_step4_int_nboth ABDC EBFD d b g h GH (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle EBFD; assumption)) (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle EBFD; assumption)) (by euclid_assumption "" (show d ≠ b; assumption)) (by euclid_assumption "" (show g.isCentre ABDC; assumption)) (by euclid_assumption "" (show h.isCentre EBFD; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)))
  have hg_in_ABDC : g.insideCircle ABDC := center_inside_circle g ABDC hcenABDC
  euclid_apply (line_from_points d b) as DB
  obtain ⟨m, hm_DB, hm_bet⟩ :=
    exists_point_between_points_on_line DB d b (by euclid_finish)
  have hm_ABDC : m.insideCircle ABDC :=
    circle_points_between d b m ABDC ⟨fun ⟨_, hc⟩ => hc hd_ABDC, fun ⟨_, hc⟩ => hc hb_ABDC, hm_bet⟩
  have hm_EBFD : m.insideCircle EBFD :=
    circle_points_between d b m EBFD ⟨fun ⟨_, hc⟩ => hc hd_EBFD, fun ⟨_, hc⟩ => hc hb_EBFD, hm_bet⟩
  obtain ⟨w', hw'_ABDC, hw'_GH, hw'_bet⟩ :=
    intersection_circle_line_extending_points ABDC GH g h ⟨hg_in_ABDC, hgGH, hhGH, hgh⟩
  by_cases hd_on : d.onLine GH
  · have hb_off : ¬b.onLine GH := fun hb => step4_int_nboth ⟨hd_on, hb⟩
    -- @args: ABDC EBFD b g h w' GH
    have step4_int_wout : w'.outsideCircle EBFD := by euclid_apply (helper_3_13_step4_int_wout ABDC EBFD b g h w' GH (by euclid_assumption "" (show b.onCircle ABDC; assumption)) (by euclid_assumption "" (show b.onCircle EBFD; assumption)) (by euclid_assumption "" (show g.isCentre ABDC; assumption)) (by euclid_assumption "" (show h.isCentre EBFD; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show w'.onCircle ABDC; assumption)) (by euclid_assumption "" (show w'.onLine GH; assumption)) (by euclid_assumption "" (show between w' g h; assumption)) (by euclid_assumption "" (show ¬b.onLine GH; assumption)))
    exact intersection_circle_circle_1 m w' ABDC EBFD
      ⟨fun ⟨hc, _⟩ => hc hm_ABDC, fun ⟨_, hc⟩ => hc hw'_ABDC, hm_EBFD, step4_int_wout⟩
  · have hd_off : ¬d.onLine GH := hd_on
    -- @args: ABDC EBFD d g h w' GH
    have step4_int_wout : w'.outsideCircle EBFD := by euclid_apply (helper_3_13_step4_int_wout ABDC EBFD d g h w' GH (by euclid_assumption "" (show d.onCircle ABDC; assumption)) (by euclid_assumption "" (show d.onCircle EBFD; assumption)) (by euclid_assumption "" (show g.isCentre ABDC; assumption)) (by euclid_assumption "" (show h.isCentre EBFD; assumption)) (by euclid_assumption "" (show g.onLine GH; assumption)) (by euclid_assumption "" (show h.onLine GH; assumption)) (by euclid_assumption "" (show g ≠ h; assumption)) (by euclid_assumption "" (show w'.onCircle ABDC; assumption)) (by euclid_assumption "" (show w'.onLine GH; assumption)) (by euclid_assumption "" (show between w' g h; assumption)) (by euclid_assumption "" (show ¬d.onLine GH; assumption)))
    exact intersection_circle_circle_1 m w' ABDC EBFD
      ⟨fun ⟨hc, _⟩ => hc hm_ABDC, fun ⟨_, hc⟩ => hc hw'_ABDC, hm_EBFD, step4_int_wout⟩

end Elements.Book3
