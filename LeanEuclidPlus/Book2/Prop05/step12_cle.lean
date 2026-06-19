import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.12 sub: between c l e — l (= KM ∩ CE) lies between c and e on the left side CE of the square.
   c and e are on opposite sides of KM: c.sameSide d KM (both on AB ∥ KM); d,g opposite across KM
   (between d h g, h ∈ KM, pasch_3); g.sameSide e KM (both on EF ∥ KM); transitivity ⟹ c,e opposite.
   pasch_4 then places l (∈ KM ∩ CE) between c and e.  Off-KM facts + KM∥EF are sub-nodes / in-body. -/
theorem helper_2_5_step12_cle (c d e g h l : Point) (AB EF KM CE DG : Line)
    (hcAB : c.onLine AB) (hdAB : d.onLine AB)
    (heEF : e.onLine EF) (hgEF : g.onLine EF)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM)
    (hlCE : l.onLine CE) (hcCE : c.onLine CE) (heCE : e.onLine CE)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG) (hgDG : g.onLine DG)
    (hdhg : between d h g)
    (hce : c ≠ e)
    (hcoffKM : ¬(c.onLine KM)) (heoffKM : ¬(e.onLine KM))
    (hdoffKM : ¬(d.onLine KM)) (hgoffKM : ¬(g.onLine KM))
    (hKMAB : ¬(KM.intersectsLine AB)) (hKMEF : ¬(KM.intersectsLine EF))
    (hKMCE : KM ≠ CE) :
    between c l e := by
  euclid_intros
  -- c.sameSide d KM (both on AB ∥ KM)
  have hcd : c.sameSide d KM := by
    by_contra hns
    euclid_apply (intersection_lines_opposing c d KM AB)
    euclid_finish
  -- d,g opposite across KM (h ∈ KM between them)
  have hdg : ¬(d.sameSide g KM) := by
    euclid_apply (pasch_3 d h g KM)
    euclid_finish
  -- g.sameSide e KM (both on EF ∥ KM)
  have hge : g.sameSide e KM := by
    by_contra hns
    euclid_apply (intersection_lines_opposing g e KM EF)
    euclid_finish
  -- c,e opposite across KM
  have hce_opp : ¬(c.sameSide e KM) := by euclid_finish
  -- l between c,e
  have hcl : c ≠ l := fun heq => hcoffKM (by rw [heq]; exact hlKM)
  have hel : e ≠ l := fun heq => heoffKM (by rw [heq]; exact hlKM)
  euclid_apply (pasch_4 c l e KM CE)
  euclid_finish

end Elements.Book2
