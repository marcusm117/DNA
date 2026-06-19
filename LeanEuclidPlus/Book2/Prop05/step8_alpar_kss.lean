import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.8 sub: k.sameSide a CE. Key chain:
   1. hcmpar gives c.sameSide l BF → c∉BF → CE≠BF.
   2. a≠c from hacd (between a c d).
   3. Assume a∈CE: two_points_determine_line a c AB CE → AB=CE → b∈CE → CE∩BF → contradicts hCEBF.
      Hence a∉CE. 4. AK≠CE (a∈AK, a∉CE). 5. k∉CE via intersection_lines_common_point.
   6. by_contra + intersection_lines_opposing k a CE AK + euclid_finish. -/
theorem helper_2_5_step8_alpar_kss (a b c d k l m : Point) (AB KM AK CE BF : Line)
    (haAB : a.onLine AB) (hcAB : c.onLine AB) (hbAB : b.onLine AB)
    (hkAK : k.onLine AK) (haAK : a.onLine AK)
    (hcCE : c.onLine CE)
    (hbBF : b.onLine BF)
    (hacd : between a c d)
    (hAKCE : ¬(AK.intersectsLine CE))
    (hCEBF : ¬(CE.intersectsLine BF))
    (hcmpar : formParallelogram c b l m AB KM CE BF) :
    k.sameSide a CE := by
  euclid_intros
  -- Step 1: c∉BF from hcmpar (c.sameSide l BF inside hcmpar)
  have hcoffBF : ¬(c.onLine BF) := by
    euclid_apply (same_side_not_on_line c l BF)
    euclid_finish
  -- Step 2: CE≠BF
  have hCEneqBF : CE ≠ BF := fun heq => hcoffBF (heq ▸ hcCE)
  -- Step 3: a≠c and a∉CE
  have hac : a ≠ c := by euclid_finish
  have haoffCE : ¬(a.onLine CE) := by
    intro haonCE
    have hABeqCE : AB = CE := by
      euclid_apply (two_points_determine_line a c AB CE)
      euclid_finish
    have hbonCE : b.onLine CE := hABeqCE ▸ hbAB
    euclid_apply (intersection_lines_common_point b CE BF)
    euclid_finish
  -- Step 4: AK≠CE
  have hAKneCE : AK ≠ CE := fun heq => haoffCE (heq ▸ haAK)
  -- Step 5: k∉CE
  have hkoffCE : ¬(k.onLine CE) := by
    intro hkon
    euclid_apply (intersection_lines_common_point k AK CE)
    euclid_finish
  -- Step 6: sameSide by contradiction
  by_contra hns
  euclid_apply (intersection_lines_opposing k a CE AK)
  euclid_finish

end Elements.Book2
