import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.11 sub-sub: f ∉ AB. f ∈ BF; b ∈ AB ∩ BF; ∠c:b:f = ∟ at b. If f ∈ AB then f,b,c collinear
   with f on BF and b on AB ∩ BF, but the right angle forces f off AB. -/
theorem helper_2_5_step11_DGneCE_foff (b c d f : Point) (AB BF : Line)
    (hbAB : b.onLine AB) (hcAB : c.onLine AB)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF)
    (hcdb : between c d b)
    (hcbf : ∠ c:b:f = ∟) (hbf_len : |(b─f)| = |(c─b)|) :
    ¬(f.onLine AB) := by
  intro hfAB
  euclid_finish

end Elements.Book2
