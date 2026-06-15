import SystemE
import Book.Prop34
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.4.22: "So, for the same (reasons), HF is also a square." HGFD (sides h─g on HK, g─f on CF,
   f─d on DE, d─h on AD) is a square. It is a parallelogram (step22_par) so |h─g| = |f─d| and
   |g─f| = |d─h|, with right angles (rectangle). Equilateral: from the rectangle ACGH (step22_acgh)
   |a─c| = |h─g| and |a─h| = |c─g|; with |c─g| = |c─b| (CGKB equilateral / step8) and the
   collinear sums |a─d| = |a─h| + |h─d| (a-h-d) and |a─b| = |a─c| + |c─b| (a-c-b) plus
   |a─d| = |a─b| (square side), we get |d─h| = |a─c| = |h─g|, so all four sides are equal. -/
set_option systemE.solverTime 30 in
theorem helper_2_4_step22 (a b c d e f g h k : Point) (AB CF AD BE HK BD DE : Line)
    (hacb : between a c b)
    (haAB : a.onLine AB) (hbAB : b.onLine AB)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hhAD : h.onLine AD)
    (heBE : e.onLine BE) (hbBE : b.onLine BE)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hfDE : f.onLine DE)
    (hbBD : b.onLine BD) (hgBD : g.onLine BD) (hdBD : d.onLine BD)
    (hgHK : g.onLine HK) (hhHK : h.onLine HK) (hkHK : k.onLine HK) (hkBE : k.onLine BE)
    (hHKAB : ¬(HK.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hCFAD : ¬(CF.intersectsLine AD)) (hDEAB : ¬(DE.intersectsLine AB))
    (hade : ∠ a:d:e = ∟)
    (hab : a ≠ b) (heb : e ≠ b) (hadab : |(a─d)| = |(a─b)|) (hdeab : |(d─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (habe : ∠ a:b:e = ∟)
    (hstep8 : |(b─c)| = |(c─g)|) :
    (|(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)|) ∧
      ((∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟)) := by
  euclid_intros
  -- distinctness / off-line roots
  have had : a ≠ d := by euclid_finish
  have hde : d ≠ e := by euclid_finish
  have hda : d ≠ a := fun h => had h.symm
  have step5_cnad : ¬(c.onLine AD) := by sorry
  have step8_dnab : ¬(d.onLine AB) := by sorry
  have step9_anbe : ¬(a.onLine BE) := by sorry
  have hbd : b ≠ d := fun hh => step8_dnab (hh ▸ hbAB)
  have step5_bgd : between b g d := by sorry
  have hbg : b ≠ g := (between_symm b g d step5_bgd).2.1
  have step9_gnab : ¬(g.onLine AB) := by sorry
  have hcAB : c.onLine AB := by euclid_apply (between_same_line_in a c b AB); euclid_finish
  have hcg : c ≠ g := fun hh => step9_gnab (hh ▸ hcAB)
  have step15_ande : ¬(a.onLine DE) := by sorry
  have hgd : g ≠ d := by euclid_finish
  have hABHK : AB ≠ HK := fun hh => step9_gnab (hh ▸ hgHK)
  -- off-HK points (a, b, d) for the foot betweenness a-h-d
  have step15_bnhk : ¬(b.onLine HK) := by sorry
  have step22_anhk : ¬(a.onLine HK) := by sorry
  have step22_dnhk : ¬(d.onLine HK) := by sorry
  have step22_abshk : a.sameSide b HK := by sorry
  -- foot betweenness on AD
  have step22_ahd : between a h d := by sorry
  have hhd : h ≠ d := by euclid_finish
  -- line distinctness for the sameSide derivations
  have hADCF : AD ≠ CF := fun hh => step5_cnad (hh ▸ hcCF)
  have hBEAD : BE ≠ AD := fun hh => step9_anbe (hh ▸ haAD)
  have step9_cnbe : ¬(c.onLine BE) := by sorry
  have hCFBE : CF ≠ BE := fun hh => step9_cnbe (hh ▸ hcCF)
  have hBECF : BE ≠ CF := fun hh => hCFBE hh.symm
  have step9_cfbe : ¬(CF.intersectsLine BE) := by sorry
  -- distinctness among the horizontals/base for HK ∥ DE
  have hDEAB' : DE ≠ AB := fun hh => step8_dnab (hh ▸ hdDE)
  have step22_hnde : ¬(h.onLine DE) := by sorry
  have hHKDE : HK ≠ DE := fun hh => step22_hnde (hh ▸ hhHK)
  -- sameSide facts (all "two points on a line ∥ CF") — reuse step22_ahcf
  have step22_ahcf : a.sameSide h CF := by sorry
  have step22_hsd : h.sameSide d CF := by sorry
  have step22_adcf : a.sameSide d CF := by sorry
  have step22_hkde : ¬(HK.intersectsLine DE) := by sorry
  have step22_becf : b.sameSide e CF := by sorry
  have step22_gf : g ≠ f := by sorry
  -- d ≠ f, e ≠ f (d ∈ AD, e ∈ BE, both ∥ CF; f ∈ CF)
  have hdnCF : ¬(d.onLine CF) := by
    intro hdCF; euclid_apply (intersection_lines_common_point d CF AD); euclid_finish
  have hdf : d ≠ f := fun hh => hdnCF (hh ▸ hfCF)
  have henCF : ¬(e.onLine CF) := by
    intro heCF; euclid_apply (intersection_lines_common_point e CF BE); euclid_finish
  have hef : e ≠ f := fun hh => henCF (hh ▸ hfCF)
  -- foot betweenness on DE (uses the sameSide facts above)
  have step22_dfe : between d f e := by sorry
  -- the two parallelograms, the equilateral, the corner angle, the right angles
  have step22_adni : ¬(AD.intersectsLine CF) := by sorry
  have step22_acgh : |(a─c)| = |(h─g)| ∧ |(a─h)| = |(c─g)| := by sorry
  have hacng : |(a─c)| = |(h─g)| := step22_acgh.1
  have hahcg : |(a─h)| = |(c─g)| := step22_acgh.2
  have step22_par : formParallelogram h g d f HK DE AD CF := by sorry
  have step22_eq : |(h─g)| = |(g─f)| ∧ |(g─f)| = |(f─d)| ∧ |(f─d)| = |(d─h)| := by sorry
  have step22_fdh : ∠ f:d:h = ∟ := by sorry
  have step22_ra : (∠ d:h:g = ∟) ∧ (∠ h:g:f = ∟) ∧ (∠ g:f:d = ∟) ∧ (∠ f:d:h = ∟) := by sorry
  exact ⟨step22_eq, step22_ra⟩

end Elements.Book2
