import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.15 sub: between b h e (b = AB∩BE, h = KM∩BE, e = EF∩BE; KM between AB and EF).
   Reuses step15_cle_opp with c→b to get ¬(b.sameSide e KM), then pasch_4 b h e KM BE closes.
   hboffKM and heoffKM taken as hyps (pre-derived in parent step15_ss_eh) to keep combine fast. -/
set_option systemE.solverTime 30 in
theorem helper_2_5_step15_bhe (b d e g h : Point) (AB BE EF KM : Line)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hgEF : g.onLine EF) (heEF : e.onLine EF)
    (hhKM : h.onLine KM)
    (hdhg : between d h g)
    (hKMEF : ¬(KM.intersectsLine EF))
    (hKMAB : ¬(KM.intersectsLine AB))
    (hboffKM : ¬(b.onLine KM))
    (heoffKM : ¬(e.onLine KM)) :
    between b h e := by
  euclid_intros
  -- @args: b d e g h AB EF KM
  have step15_cle_opp : ¬(b.sameSide e KM) := by sorry
  have hKMneBE : KM ≠ BE := fun heq => hboffKM (heq ▸ hbBE)
  have hbh : b ≠ h := fun heq => hboffKM (heq ▸ hhKM)
  have heh : e ≠ h := fun heq => heoffKM (heq ▸ hhKM)
  euclid_apply (pasch_4 b h e KM BE)
  euclid_finish

end Elements.Book2
