import SystemE
import Book1.Prop47.Main
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

open Elements.Book1

theorem helper_3_36_step28 (b d e : Point) (ABC : Circle) (DB EB ED : Line)
  (hassump1 : ∠ e:b:d = ∟)
  (he_centre : e.isCentre ABC) (hb_circ : b.onCircle ABC)
  (hd_out : ¬ d.insideCircle ABC) (hd_noncirc : ¬ d.onCircle ABC)
  (hb_DB : b.onLine DB) (hd_DB : d.onLine DB) (hnint : ¬DB.intersectsCircle ABC)
  (he_EB : e.onLine EB) (hb_EB : b.onLine EB) (he_ED : e.onLine ED) (hd_ED : d.onLine ED)
  : |(e─b)| * |(e─b)| + |(d─b)| * |(d─b)| = |(e─d)| * |(e─d)| := by
  have hne_DB : ¬ e.onLine DB := by euclid_finish
  euclid_apply (proposition_47 b e d EB ED DB)
  euclid_finish

end Elements.Book3
