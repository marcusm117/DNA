import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_15_hstep4_pts_lin
    (e k l f h : Point) (ABCD : Circle) (FG EK : Line)
    (h_centre : e.isCentre ABCD)
    (h_f_circ : f.onCircle ABCD)
    (hEK : distinctPointsOnLine e k EK)
    (h_k_fg : k.onLine FG)
    (h_f_fg : f.onLine FG)
    (h_angle_ekf : ∠ e:k:f = ∟)
    (h_el_eq : |(e─l)| = |(e─h)|)
    (h_eh_lt_ek : |(e─h)| < |(e─k)|) :
    l.insideCircle ABCD := by
  have h_el_lt_ek : |(e─l)| < |(e─k)| := h_el_eq ▸ h_eh_lt_ek
  apply point_in_circle_if e f l ABCD
  refine ⟨h_centre, h_f_circ, ?_⟩
  by_cases h_kf : k = f
  · have h_kef : |(e─k)| = |(e─f)| := by simp only [h_kf]
    linarith
  · have h_e_inside : e.insideCircle ABCD := center_inside_circle e ABCD h_centre
    have h_e_not_on : ¬(e.onCircle ABCD) := inside_not_on_circle e ABCD h_e_inside
    have h_ef : e ≠ f := fun h => h_e_not_on (h ▸ h_f_circ)
    euclid_apply (line_from_points e f) as EF
    have h_ke : distinctPointsOnLine k e EK := by euclid_finish
    have h_tri : formTriangle k e f EK EF FG :=
      ⟨h_ke, by assumption, by assumption, h_f_fg, h_k_fg,
       by euclid_finish, by euclid_finish, by euclid_finish⟩
    have h_pyth : |(e─f)| * |(e─f)| = |(e─k)| * |(e─k)| + |(k─f)| * |(k─f)| :=
      Elements.Book1.proposition_47 k e f EK EF FG ⟨h_tri, h_angle_ekf⟩
    have h_kf_ne : |(k─f)| ≠ 0 := fun h => h_kf (zero_segment_if k f h)
    have h_kf_pos : 0 < |(k─f)| := lt_of_le_of_ne (segment_gte_zero _) (Ne.symm h_kf_ne)
    have h_ef_nn := segment_gte_zero (e─f)
    have h_ek_nn := segment_gte_zero (e─k)
    have h_ek_lt_ef : |(e─k)| < |(e─f)| := by nlinarith
    linarith

end Elements.Book3
