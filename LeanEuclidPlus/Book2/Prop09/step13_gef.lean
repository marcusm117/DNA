import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements

-- step13 helper: ∠g:e:f = ∠c:e:b (g on ray c→e, f on ray e→b, so equal_angles).
theorem helper_2_9_step13_gef
  (a b c e f g e0 e1 : Point) (AB CE EB : Line)
  (hab_a : a.onLine AB) (hab_c : c.onLine AB) (hab_b : b.onLine AB)
  (heb_e : e.onLine EB) (heb_f : f.onLine EB) (heb_b : b.onLine EB)
  (hce_c : c.onLine CE) (hce_e0 : e0.onLine CE) (hce_e1 : e1.onLine CE) (hce_g : g.onLine CE)
  (hne0 : ¬e0.onLine AB)
  (hbte : between c e e1)
  (hbegc : between e g c)
  (hbefb : between e f b) :
  ∠ g:e:f = ∠ c:e:b := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  euclid_apply (equal_angles e g c f b CE EB)
  euclid_finish

end Elements.Book2
