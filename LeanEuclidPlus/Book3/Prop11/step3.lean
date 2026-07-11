import SystemE
import Book1.Prop20.Main
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_11_step3 (a f g h : Point) (ABC : Circle) (AF AG : Line)
    (left : a.onCircle ABC) (left_5 : f.isCentre ABC)
    (left_4 : |(g─a)| < |(f─a)|)
    (haf1 : a.onLine AF) (haf2 : f.onLine AF)
    (hag1 : a.onLine AG) (hag2 : g.onLine AG)
    (hsuppose1 : ¬between f g a)
    (h_ne : h ≠ a) (h_on_ABC : h.onCircle ABC) (h_bet_fgh : between f g h)
    (hassump1 : |(f─a)| = |(f─h)|)
    (hassump2 : |(a─g)| + |(g─f)| > |(f─h)|)
    : |(a─g)| > |(f─h)| - |(g─f)| := by
  euclid_apply (line_from_points f g) as FG
  euclid_apply (Elements.Book1.proposition_20 g a f AG AF FG)
  linarith

end Elements.Book3
