import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book3

theorem helper_3_2_step9_tri (d p b : Point) (DFE PB DB : Line)
    (hdDFE : d.onLine DFE) (hpDFE : p.onLine DFE)
    (hdDB : d.onLine DB) (hbDB : b.onLine DB)
    (hpPB : p.onLine PB) (hbPB : b.onLine PB)
    (hdp_ne : d ≠ p) (hdb_ne : d ≠ b) (hpb_ne : p ≠ b)
    (hd_PB : ¬d.onLine PB) :
    formTriangle d p b DFE PB DB := by
  have hDFE_ne_PB : DFE ≠ PB := fun h => absurd (h ▸ hdDFE) hd_PB
  have hPB_ne_DB : PB ≠ DB := fun h => absurd (h.symm ▸ hdDB) hd_PB
  have hDB_ne_DFE : DB ≠ DFE := by
    intro hEQ
    have hponDB : p.onLine DB := hEQ.symm ▸ hpDFE
    have hDisPB : distinctPointsOnLine p b PB := by euclid_finish
    have hPBeqDB : PB = DB :=
      two_points_determine_line p b PB DB ⟨hDisPB, hponDB, hbDB⟩
    exact hd_PB (hPBeqDB.symm ▸ hdDB)
  euclid_finish

end Elements.Book3
