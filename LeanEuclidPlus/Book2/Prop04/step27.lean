import SystemE

namespace Elements.Book2

-- 2.4.27: the four figures HF, CK, AG, GE make up the whole square ADEB = |AB|².
-- Combines two sub-lemmas (applied internally): step27_decomp (the four sub-figure areas sum to
-- the big square's area) and step27_bigsq (area of ADEB = |AB|²).
set_option systemE.solverTime 30 in
theorem helper_2_step27 (a b c d e f g h k : Point) (AB DE AD BE CF HK BD : Line)
    (hbig : formParallelogram d e a b DE AB AD BE)
    (hde : |(d─e)| = |(a─b)|) (had : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟)
    (hacb : between a c b) (hdfe : between d f e)
    (hahd : between a h d) (hbke : between b k e)
    (hcgf : between c g f) (hhgk : between h g k)
    (hcCF : c.onLine CF) (hgCF : g.onLine CF) (hfCF : f.onLine CF)
    (hhHK : h.onLine HK) (hgHK : g.onLine HK) (hkHK : k.onLine HK)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (haAD : a.onLine AD) (hdAD : d.onLine AD) (hbBE : b.onLine BE) (heBE : e.onLine BE)
    (hADCF : ¬(AD.intersectsLine CF)) (hCFBE : ¬(CF.intersectsLine BE)) :
    (Triangle.area △ h:g:f + Triangle.area △ h:f:d) +
    (Triangle.area △ c:b:k + Triangle.area △ c:k:g) +
    (Triangle.area △ a:c:g + Triangle.area △ a:g:h) +
    (Triangle.area △ g:k:e + Triangle.area △ g:e:f) = |(a─b)| * |(a─b)| := by
  euclid_intros
  euclid_apply (helper_2_step27_decomp a b c d e f g h k AB DE AD BE CF HK BD)
  euclid_apply (helper_2_step27_bigsq a b d e AB DE AD BE)
  euclid_finish

end Elements.Book2
