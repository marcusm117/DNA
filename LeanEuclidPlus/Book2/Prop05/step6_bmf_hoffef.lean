import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: ¬h.onLine EF. h ∈ DG and g ∈ DG ∩ EF; DG ≠ EF, and h ≠ g, so h on EF would make the
   distinct lines DG, EF share two points. Simpler: h ∈ BE between b and e (between b h e), e ∈ EF,
   and the diagonal BE meets EF only at e; if h ∈ EF then h = e (both on BE∩EF), contradicting
   between b h e (h ≠ e). Uses BE ≠ EF (b ∈ BE off EF). -/
theorem helper_2_5_step6_bmf_hoffef (b e h : Point) (BE EF : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (heEF : e.onLine EF) (hboffEF : ¬(b.onLine EF)) (hbhe : between b h e) :
    ¬(h.onLine EF) := by
  intro hhEF
  have hbe_ne_ef : BE ≠ EF := fun heq => hboffEF (heq ▸ hbBE)
  euclid_finish

end Elements.Book2
