import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_22_hcut
    (d e f g h i : Point) (DE : Line) (DKL KLH : Circle)
    (a a' b b' c c' : Point)
    (hcenF : f.isCentre DKL) (hdOnDKL : d.onCircle DKL)
    (hcenG : g.isCentre KLH) (hhOnKLH : h.onCircle KLH)
    (hiOnKLH : i.onCircle KLH)
    (hdDE : d.onLine DE) (heDE : e.onLine DE)
    (hbet_dfe : between d f e) (hbet_fge : between f g e) (hbet_ghe : between g h e)
    (hbet_igh : between i g h)
    (hdf : |(d─f)| = |(a─a')|) (hfg : |(f─g)| = |(b─b')|) (hgh : |(g─h)| = |(c─c')|)
    (htri1 : |(a─a')| + |(b─b')| > |(c─c')|)
    (htri2 : |(a─a')| + |(c─c')| > |(b─b')|)
    (htri3 : |(b─b')| + |(c─c')| > |(a─a')|) :
    KLH.intersectsCircle DKL := by
  euclid_finish

end Elements.Book1
