import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: between c l e. l = KM ∩ CE; c is the base foot of CE (on AB), e the top corner
   (on EF). KM (∥ AB, through h) crosses CE strictly between c and e because b,e lie on opposite
   sides of KM (h between them, h ∈ KM) and c shares b's side. pasch_4 then places l between c,e.
   The off-KM facts and point-distinctness come in as hyps (supplied/derived by the parent). -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step8_cle (b c e h l m : Point) (CE KM AB EF BE : Line)
    (hcCE : c.onLine CE) (heCE : e.onLine CE) (hlCE : l.onLine CE)
    (hlKM : l.onLine KM) (hhKM : h.onLine KM) (hmKM : m.onLine KM)
    (hcAB : c.onLine AB) (heEF : e.onLine EF)
    (hhBE : h.onLine BE) (heBE : e.onLine BE)
    (hKMAB : ¬(KM.intersectsLine AB))
    (hKMEF : ¬(KM.intersectsLine EF))
    (hcoffKM : ¬(c.onLine KM)) (heoffKM : ¬(e.onLine KM))
    (hbBE : b.onLine BE) (hbAB : b.onLine AB) (hbhe : between b h e) :
    between c l e := by
  euclid_intros
  have hKMneCE : KM ≠ CE := fun heq => hcoffKM (heq ▸ hcCE)
  -- point-distinctness: l ∈ KM but c,e ∉ KM, so l ≠ c and l ≠ e; c ≠ e since c ∈ AB, e ∉ AB-side
  have hcl : c ≠ l := fun heq => hcoffKM (heq ▸ hlKM)
  have hle : l ≠ e := fun heq => heoffKM (heq ▸ hlKM)
  have hce : c ≠ e := by euclid_finish
  -- b, e opposite across KM: h on KM is between b and e (between b h e)
  have hbe_opp : ¬(b.sameSide e KM) := by
    euclid_apply (pasch_3 b h e KM)
    euclid_finish
  -- c shares b's side of KM (both on AB ∥ KM), so c, e opposite across KM
  have hbc_same : b.sameSide c KM := by
    by_contra hns
    euclid_apply (intersection_lines_opposing b c KM AB)
    euclid_finish
  have hopp : ¬(c.sameSide e KM) := by euclid_finish
  euclid_apply (pasch_4 c l e KM CE)
  euclid_finish

end Elements.Book2
