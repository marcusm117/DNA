import SystemE
import Mathlib.Tactic.Linarith

namespace Elements.Book2

-- 2.4.27: the four figures HF, CK, AG, GE make up the whole square ADEB = |AB|².
-- Combines two sub-lemmas (applied internally): step27_decomp (the four sub-figure areas sum to
-- the big square's area) and step27_bigsq (area of ADEB = |AB|²).
set_option systemE.solverTime 30 in
-- The `formParallelogram d e a b DE AB AD BE` is passed as its atomic conjuncts (Main supplies those
-- directly); the packaged abbrev is NOT a named hyp at the call site and the SMT translator can't
-- prove it (`Unexpected application formParallelogram`). The body reassembles it for step27_bigsq.
theorem helper_2_step27 (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
    (hdaBE : d.sameSide a BE) (heb : e ≠ b)
    (hDEAB : ¬(DE.intersectsLine AB)) (hADBE : ¬(AD.intersectsLine BE))
    (hde : |(d─e)| = |(a─b)|) (had : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟)
    (hacb : between a c b)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (hhHK : h.onLine HK) (hgHK : g.onLine HK) (hkHK : k.onLine HK)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hkBE : k.onLine BE) (hbBD : b.onLine BD) (hdBD : d.onLine BD) (hgBD : g.onLine BD)
    (hacDE : a.sameSide c DE) (hcbDE : c.sameSide b DE)
    (hdf : d ≠ f) (hfe : f ≠ e)
    (hbd : b ≠ d) (hbg : b ≠ g) (hdg : d ≠ g) (hCFBD : CF ≠ BD)
    (hah : a ≠ h) (hdh : d ≠ h) (hADHK : AD ≠ HK)
    (hbk : b ≠ k) (hek : e ≠ k) (hBEHK : BE ≠ HK)
    (hef : e ≠ f) (hDECF : DE ≠ CF)
    (hcg : c ≠ g) (hfg : f ≠ g) (hCFHK : CF ≠ HK)
    (hhg : h ≠ g) (hkg : k ≠ g) (hHKCF : HK ≠ CF)
    (hCFBE : CF ≠ BE) (hHKDE : HK ≠ DE) (hABHKne : AB ≠ HK) (hADCFne : AD ≠ CF)
    (hADCF : ¬(AD.intersectsLine CF)) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
    (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
    (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
    (Triangle.area △ g:k:e + Triangle.area △ g:e:f) = |(a─b)| * |(a─b)| := by
  euclid_intros
  -- betweenness facts (pasch-derived) the step27_decomp cuts consume; supplied to it as hyps
  have positions : between a h d ∧ between b k e ∧ between d f e ∧
      between b g d ∧ between c g f ∧ between h g k := by sorry
  -- @args: a b c d e f g h k AB DE AD BE CF HK
  have step27_decomp :
      (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
      (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
      (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
      (Triangle.area △ g:k:e + Triangle.area △ g:e:f) =
      Triangle.area △ d:a:b + Triangle.area △ d:b:e := by sorry
  -- @args: a b d e AB DE AD BE
  have step27_bigsq :
      Triangle.area △ d:a:b + Triangle.area △ d:b:e = |(a─b)| * |(a─b)| := by sorry
  -- combine: transitivity of the two area-equalities — pure algebra, no SMT over area atoms
  linarith [step27_decomp, step27_bigsq]

end Elements.Book2
