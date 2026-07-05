import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

set_option systemE.solverTime 30 in
theorem helper_1_35_step14
  (a d e f b c g : Point) (AF BC AB CD EB FC : Line)
  (hassump1 : formParallelogram a d b c AF BC AB CD)
  (he_AF : e.onLine AF) (hf_AF : f.onLine AF)
  (he_EB : e.onLine EB) (hb_EB : b.onLine EB)
  (hf_FC : f.onLine FC) (hc_FC : c.onLine FC)
  (hg_CD : g.onLine CD) (hg_EB : g.onLine EB)
  (hbet1 : between a d e) (hbet2 : between d e f)
  (hno_EB_FC : ¬EB.intersectsLine FC)
  (hesid : e.sameSide b FC)
  (hfc : f ≠ c)
  (h13 : Triangle.area △ a:b:d + Triangle.area △ b:g:d + Triangle.area △ g:b:c =
         Triangle.area △ e:g:c + Triangle.area △ e:c:f + Triangle.area △ g:b:c)
  : Triangle.area △ a:b:d + Triangle.area △ d:b:c = Triangle.area △ e:b:c + Triangle.area △ e:c:f := by
  -- Re-derive between e g b (same approach as step12)
  have hd_CD : d.onLine CD := hassump1.2.2.2.2.2.2.1.1
  have hpasch_aed : ¬(a.sameSide e CD) := pasch_3 a d e CD ⟨hbet1, hd_CD⟩
  have hassoc_ab : a.sameSide b CD := hassump1.2.2.2.2.2.2.2.1
  have hne_e_ss_b_CD : ¬(e.sameSide b CD) := fun hess =>
    hpasch_aed (same_side_trans b a e CD
      ⟨same_side_symm a b CD hassoc_ab, same_side_symm e b CD hess⟩)
  have he_ne_g : e ≠ g := by euclid_finish
  have hb_ne_g : b ≠ g := by euclid_finish
  have heb_ne : e ≠ b := by euclid_finish
  have hdist_eb : distinctPointsOnLine e b EB := ⟨he_EB, hb_EB, heb_ne⟩
  have hCD_ne_EB : CD ≠ EB := by euclid_finish
  have hbetegb : between e g b :=
    pasch_4 e g b CD EB ⟨hCD_ne_EB, hg_CD, hg_EB, hdist_eb, he_ne_g, hb_ne_g, hne_e_ss_b_CD⟩
  -- Re-derive between d g c (same approach as step12)
  have hno_AF_BC : ¬AF.intersectsLine BC := hassump1.2.2.2.2.2.2.2.2.1
  have hassump2 : formParallelogram e f b c AF BC EB FC :=
    ⟨he_AF, hf_AF, hassump1.2.2.1, hassump1.2.2.2.1, he_EB, hb_EB, ⟨hf_FC, hc_FC, hfc⟩, hesid, hno_AF_BC, hno_EB_FC⟩
  have hfcss_EB : f.sameSide c EB := (parallelogram_same_side e f b c AF BC EB FC hassump2).1
  have hpasch_def : ¬(d.sameSide f EB) := pasch_3 d e f EB ⟨hbet2, he_EB⟩
  have hne_d_ss_c_EB : ¬(d.sameSide c EB) := fun hdss =>
    hpasch_def (same_side_trans c d f EB
      ⟨same_side_symm d c EB hdss, same_side_symm f c EB hfcss_EB⟩)
  have hd_ne_g : d ≠ g := by euclid_finish
  have hc_ne_g : c ≠ g := by euclid_finish
  have hdc_ne : d ≠ c := hassump1.2.2.2.2.2.2.1.2.2
  have hc_CD : c.onLine CD := hassump1.2.2.2.2.2.2.1.2.1
  have hdist_dc : distinctPointsOnLine d c CD := ⟨hd_CD, hc_CD, hdc_ne⟩
  have hbetdgc : between d g c :=
    pasch_4 d g c EB CD ⟨hCD_ne_EB.symm, hg_EB, hg_CD, hdist_dc, hd_ne_g, hc_ne_g, hne_d_ss_c_EB⟩
  -- Off-line facts for sum_areas_if
  have hb_not_CD : ¬b.onLine CD := by euclid_finish
  have hc_not_EB : ¬c.onLine EB := by euclid_finish
  -- Decompose △dbc: b off CD, between d g c on CD
  have hsplit_dbc : Triangle.area △ d:g:b + Triangle.area △ b:g:c = Triangle.area △ d:b:c :=
    sum_areas_if d c g b CD ⟨hd_CD, hc_CD, hg_CD, hdc_ne, hd_ne_g, hc_ne_g, hb_not_CD, hbetdgc⟩
  -- Decompose △ebc: c off EB, between e g b on EB
  have hsplit_ebc : Triangle.area △ e:g:c + Triangle.area △ c:g:b = Triangle.area △ e:c:b :=
    sum_areas_if e b g c EB ⟨he_EB, hb_EB, hg_EB, heb_ne, he_ne_g, hb_ne_g, hc_not_EB, hbetegb⟩
  -- Area symmetry
  have hs_dgb : Triangle.area △ d:g:b = Triangle.area △ b:g:d := by euclid_finish
  have hs_bgc : Triangle.area △ b:g:c = Triangle.area △ g:b:c := by euclid_finish
  have hs_cgb : Triangle.area △ c:g:b = Triangle.area △ g:b:c := by euclid_finish
  have hs_ecb : Triangle.area △ e:c:b = Triangle.area △ e:b:c := by euclid_finish
  linarith

end Elements.Book1
