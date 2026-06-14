import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.4.15 sub: k (= HK ∩ BE) is between b and e on the right side BE. HK separates b from e:
   • along the diagonal BD, g (∈ HK) is between b and d (step5_bgd), so b and d are on opposite
     sides of HK (pasch_3);
   • d and e both lie on DE ∥ HK (step15_dehk via Prop.~1.30), so d and e are on the same side of HK
     (step15_dse);
   hence b and e are on opposite sides of HK, and the crossing point k of BE with HK lies between
   them (pasch_4). The off-line points b∉HK, d∉HK, g∉AB, a∉DE give the line distinctness. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step15_bke (a b d e g k : Point) (BE HK DE BD AB CF AD : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hkBE : k.onLine BE)
    (hgHK : g.onLine HK) (hkHK : k.onLine HK)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hHKAB : ¬(HK.intersectsLine AB)) (hDEAB : ¬(DE.intersectsLine AB))
    (hbgd : between b g d) (hde : d ≠ e)
    (hgnAB : ¬(g.onLine AB)) (hdnAB : ¬(d.onLine AB)) :
    between b k e := by
  euclid_intros
  -- distinctness d ≠ g from between b g d
  have hdg : d ≠ g := by euclid_finish
  -- off-line points and line distinctness
  have step15_bnhk : ¬(b.onLine HK) := by sorry
  have step15_dnhk : ¬(d.onLine HK) := by sorry
  have step15_ande : ¬(a.onLine DE) := by sorry
  have hDEHK : DE ≠ HK := fun h => step15_dnhk (h ▸ hdDE)
  have hHKAB' : HK ≠ AB := fun h => hgnAB (h ▸ hgHK)
  have hABDE : AB ≠ DE := fun h => step15_ande (h ▸ haAB)
  -- b ≠ k since b ∉ HK, k ∈ HK
  have hbk : b ≠ k := fun h => step15_bnhk (h ▸ hkHK)
  -- DE ∥ HK and hence d.sameSide e HK; also e ∉ HK ⟹ e ≠ k
  have step15_dehk : ¬(DE.intersectsLine HK) := by sorry
  have henhk : ¬(e.onLine HK) := by
    intro hon; euclid_apply (intersection_lines_common_point e DE HK); euclid_finish
  have hek : e ≠ k := fun h => henhk (h ▸ hkHK)
  have step15_dse : d.sameSide e HK := by sorry
  -- b, d on opposite sides of HK (g between them, g ∈ HK); k between b, e
  euclid_apply (pasch_3 b g d HK)
  euclid_apply (pasch_4 b k e HK BE)
  euclid_finish

end Elements.Book2
