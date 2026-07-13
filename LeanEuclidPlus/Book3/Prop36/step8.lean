import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step8 (b d f : Point) (ABC : Circle) (FB DA DB : Line)
    (hbFB : b.onLine FB) (hfFB : f.onLine FB)
    (hfDA : f.onLine DA) (hdDA : d.onLine DA)
    (hbDB : b.onLine DB) (hdDB : d.onLine DB)
    (hb_circ : b.onCircle ABC) (hf_centre : f.isCentre ABC)
    (hd_out : ¬ d.insideCircle ABC) (hd_noncirc : ¬ d.onCircle ABC)
    (hangle : ∠ f:b:d = ∟) :
    |(f─d)| * |(f─d)| = |(f─b)| * |(f─b)| + |(d─b)| * |(d─b)| := by
  have hboff : ¬ b.onLine DA := by euclid_finish
  euclid_apply (proposition_47 b f d FB DA DB)
  euclid_finish

end Elements.Book3
