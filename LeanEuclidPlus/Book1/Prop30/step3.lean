import SystemE
import Book1.Prop29.variants
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_30_step3
    (EF CD GK : Line) (c d e f g h k : Point)
    (he_EF : e.onLine EF) (hf_EF : f.onLine EF) (hh_EF : h.onLine EF)
    (hc_CD : c.onLine CD) (hd_CD : d.onLine CD) (hk_CD : k.onLine CD)
    (hg_GK : g.onLine GK) (hh_GK : h.onLine GK) (hk_GK : k.onLine GK)
    (hbetw_ehf : between e h f)
    (hbetw_ckd : between c k d)
    (hbetw_ghk : between g h k)
    (heside : e.sameSide a GK)
    (hcside : c.sameSide a GK)
    (hnopar : ¬CD.intersectsLine EF)
    (hassump1 : EF.intersectsLine GK ∧ CD.intersectsLine GK ∧ ¬(CD.intersectsLine EF))
    : ∠ g:h:f = ∠ g:k:d := by
  -- f and d are both opposite a of GK (hence same side as each other)
  have hfd : f.sameSide d GK := by euclid_finish
  -- prop29' for EF ∥ CD: second conjunct gives ∠ g:h:f = ∠ h:k:d
  euclid_apply (proposition_29' e f c d g h k EF CD GK)
  -- between g h k means ray kh = ray kg, so ∠ h:k:d = ∠ g:k:d
  euclid_finish

end Elements.Book1
