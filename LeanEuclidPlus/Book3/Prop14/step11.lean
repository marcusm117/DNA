import SystemE
import Book1.Prop47.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

-- Pythagoras (I.47) for the right triangle g-c-e (right angle at g).
theorem helper_3_14_step11
    (c d e g : Point) (ABDC : Circle) (CD : Line)
    (hc : c.onCircle ABDC) (hcen : e.isCentre ABDC)
    (hcCD : c.onLine CD) (hgCD : g.onLine CD)
    (hcgd : between c g d) (heg : e ≠ g)
    (hassump1 : ∠ c:g:e = ∟) :
    |(e─g)| * |(e─g)| + |(g─c)| * |(g─c)| = |(e─c)| * |(e─c)| := by
  euclid_apply (line_from_points c e) as CE
  euclid_apply (line_from_points g e) as GE
  have h_e_off : ¬ e.onLine CD := by euclid_finish
  have htri : formTriangle g c e CD CE GE := by euclid_finish
  have hp : |(c─e)| * |(c─e)| = |(c─g)| * |(c─g)| + |(g─e)| * |(g─e)| := by
    euclid_apply (Elements.Book1.proposition_47 g c e CD CE GE)
    euclid_finish
  have h1 : |(e─g)| = |(g─e)| := segment_symmetric e g
  have h2 : |(g─c)| = |(c─g)| := segment_symmetric g c
  have h3 : |(e─c)| = |(c─e)| := segment_symmetric e c
  rw [h1, h2, h3]; linarith [hp]

end Elements.Book3
