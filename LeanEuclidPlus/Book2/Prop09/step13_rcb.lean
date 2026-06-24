import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

-- step13 helper: ∠g:c:b = ∟. CE⊥AB (step1 ∠a:c:e = ∟, with between a c b); g is on ray
-- c→e (between e g c), so ∠g:c:b = ∠e:c:b = ∟.
theorem helper_2_9_step13_rcb
  (a b c e g e1 : Point) (AB CE : Line)
  (hab_a : a.onLine AB) (hab_b : b.onLine AB) (hab_c : c.onLine AB)
  (hce_c : c.onLine CE) (hce_g : g.onLine CE) (hce_e1 : e1.onLine CE)
  (hacb : between a c b)
  (hbte : between c e e1)
  (hbegc : between e g c)
  (hstep1 : ∠ a:c:e = ∟) :
  ∠ g:c:b = ∟ := by
  have heCE : e.onLine CE := by
    euclid_apply (between_same_line_in c e e1 CE)
    assumption
  euclid_finish

end Elements.Book2
