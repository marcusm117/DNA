import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_39_step5_triEBC
    (a e b c d : Point) (BD BC EC AE CD : Line)
    (heBD : e.onLine BD) (hbBD : b.onLine BD) (hdBD : d.onLine BD)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC)
    (hcEC : c.onLine EC) (heEC : e.onLine EC)
    (hBDBC : BD ≠ BC)
    (hcCD : c.onLine CD) (hdCD : d.onLine CD) (hCDBD : CD ≠ BD) (hdbne : d ≠ b)
    (haAE : a.onLine AE) (heAE : e.onLine AE) (hassump1 : ¬(AE.intersectsLine BC))
    (hasdBC : a.sameSide d BC) :
    formTriangle e b c BD BC EC := by
  -- AE ≠ BC: a is on AE but off BC
  have hAEneBC : AE ≠ BC :=
    fun h => (same_side_not_on_line a d BC hasdBC) (h ▸ haAE)
  -- b ≠ c: if b=c then b,d on both CD and BD → CD=BD, contradicts hCDBD
  have hbcne : b ≠ c := by
    intro hbc; subst hbc
    exact hCDBD (by euclid_finish)
  -- e ≠ b: e is on AE ∥ BC, b is on BC → e ∉ BC → e ≠ b
  have hbene : e ≠ b := by
    intro heb
    have heBC : e.onLine BC := heb ▸ hbBC
    exact hassump1 (by euclid_apply (intersection_lines_common_point e AE BC); euclid_finish)
  -- BC ≠ EC: if BC=EC then e.onLine BC → AE meets BC
  have hBCEC : BC ≠ EC := by
    intro h
    have heBC : e.onLine BC := h.symm ▸ heEC
    exact hassump1 (by euclid_apply (intersection_lines_common_point e AE BC); euclid_finish)
  -- EC ≠ BD: if EC=BD then c.onLine BD, with b.onLine BD ∩ BC and b ≠ c → BD=BC
  have hECBD : EC ≠ BD := by
    intro h
    have hcBD : c.onLine BD := h.symm ▸ hcEC
    exact hBDBC (by euclid_finish)
  exact ⟨⟨heBD, hbBD, hbene⟩, hbBC, hcBC, hcEC, heEC, hBDBC, hBCEC, hECBD⟩

end Elements.Book1
