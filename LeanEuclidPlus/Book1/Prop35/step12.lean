import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_35_step12
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
  (h11 : Triangle.area △ e:a:b - Triangle.area △ d:g:e = Triangle.area △ d:f:c - Triangle.area △ d:g:e)
  : Triangle.area △ a:b:d + Triangle.area △ b:g:d = Triangle.area △ e:g:c + Triangle.area △ e:c:f := by
  -- Establish ¬(e.sameSide b CD)
  have hd_CD : d.onLine CD := hassump1.2.2.2.2.2.2.1.1
  have hpasch_aed : ¬(a.sameSide e CD) := pasch_3 a d e CD ⟨hbet1, hd_CD⟩
  have hassoc_ab : a.sameSide b CD := hassump1.2.2.2.2.2.2.2.1
  have hne_e_ss_b_CD : ¬(e.sameSide b CD) := fun hess =>
    hpasch_aed (same_side_trans b a e CD
      ⟨same_side_symm a b CD hassoc_ab, same_side_symm e b CD hess⟩)
  -- Establish between e g b via pasch_4 (L=CD, M=EB): a=e, b=g, c=b
  have he_ne_g : e ≠ g := by euclid_finish
  have hb_ne_g : b ≠ g := by euclid_finish
  have heb_ne : e ≠ b := by euclid_finish
  have hdist_eb : distinctPointsOnLine e b EB := ⟨he_EB, hb_EB, heb_ne⟩
  have hCD_ne_EB : CD ≠ EB := by euclid_finish
  have hbetegb : between e g b :=
    pasch_4 e g b CD EB ⟨hCD_ne_EB, hg_CD, hg_EB, hdist_eb, he_ne_g, hb_ne_g, hne_e_ss_b_CD⟩
  -- Establish f.sameSide c EB (from second parallelogram)
  have hno_AF_BC : ¬AF.intersectsLine BC := hassump1.2.2.2.2.2.2.2.2.1
  have hassump2 : formParallelogram e f b c AF BC EB FC :=
    ⟨he_AF, hf_AF, hassump1.2.2.1, hassump1.2.2.2.1, he_EB, hb_EB, ⟨hf_FC, hc_FC, hfc⟩, hesid, hno_AF_BC, hno_EB_FC⟩
  have hfcss_EB : f.sameSide c EB := (parallelogram_same_side e f b c AF BC EB FC hassump2).1
  -- Establish ¬(d.sameSide c EB)
  have hpasch_def : ¬(d.sameSide f EB) := pasch_3 d e f EB ⟨hbet2, he_EB⟩
  have hne_d_ss_c_EB : ¬(d.sameSide c EB) := fun hdss =>
    hpasch_def (same_side_trans c d f EB
      ⟨same_side_symm d c EB hdss, same_side_symm f c EB hfcss_EB⟩)
  -- Establish between d g c via pasch_4 (L=EB, M=CD): a=d, b=g, c=c
  have hd_ne_g : d ≠ g := by euclid_finish
  have hc_ne_g : c ≠ g := by euclid_finish
  have hdc_ne : d ≠ c := hassump1.2.2.2.2.2.2.1.2.2
  have hc_CD : c.onLine CD := hassump1.2.2.2.2.2.2.1.2.1
  have hdist_dc : distinctPointsOnLine d c CD := ⟨hd_CD, hc_CD, hdc_ne⟩
  have hbetdgc : between d g c :=
    pasch_4 d g c EB CD ⟨hCD_ne_EB.symm, hg_EB, hg_CD, hdist_dc, hd_ne_g, hc_ne_g, hne_d_ss_c_EB⟩
  -- Off-line facts
  have hb_not_AF : ¬b.onLine AF := by euclid_finish
  have hd_not_EB : ¬d.onLine EB := by euclid_finish
  have hc_not_AF : ¬c.onLine AF := by euclid_finish
  have he_not_CD : ¬e.onLine CD := by euclid_finish
  -- Distinctness for sum_areas_if
  have had_ne : a ≠ d := (between_symm a d e hbet1).2.1
  have hae_ne : a ≠ e := (between_symm a d e hbet1).2.2.1
  have hde_ne : d ≠ e := by euclid_finish
  have hdf_ne : d ≠ f := (between_symm d e f hbet2).2.2.1
  have hfe_ne : f ≠ e := (between_symm f e d (between_symm d e f hbet2).1).2.1
  -- Area decomposition of △EAB: split at d on AF, then at g on EB
  -- sum_areas_if a b c d L: between a c b, d off L; gives △a:c:d + △d:c:b = △a:d:b
  have hsplit1 : Triangle.area △ a:d:b + Triangle.area △ b:d:e = Triangle.area △ a:b:e :=
    sum_areas_if a e d b AF ⟨hassump1.1, he_AF, hassump1.2.1, hae_ne, had_ne, hde_ne.symm, hb_not_AF, hbet1⟩
  have hsplit2 : Triangle.area △ e:g:d + Triangle.area △ d:g:b = Triangle.area △ e:d:b :=
    sum_areas_if e b g d EB ⟨he_EB, hb_EB, hg_EB, heb_ne, he_ne_g, hb_ne_g, hd_not_EB, hbetegb⟩
  -- Area decomposition of △DFC: split at e on AF, then at g on CD
  have hsplit3 : Triangle.area △ d:e:c + Triangle.area △ c:e:f = Triangle.area △ d:c:f :=
    sum_areas_if d f e c AF ⟨hassump1.2.1, hf_AF, he_AF, hdf_ne, hde_ne, hfe_ne, hc_not_AF, hbet2⟩
  have hsplit4 : Triangle.area △ d:g:e + Triangle.area △ e:g:c = Triangle.area △ d:e:c :=
    sum_areas_if d c g e CD ⟨hd_CD, hc_CD, hg_CD, hdc_ne, hd_ne_g, hc_ne_g, he_not_CD, hbetdgc⟩
  -- Area symmetry
  have hs_eab : Triangle.area △ e:a:b = Triangle.area △ a:b:e := by euclid_finish
  have hs_bde : Triangle.area △ b:d:e = Triangle.area △ e:d:b := by euclid_finish
  have hs_egd : Triangle.area △ e:g:d = Triangle.area △ d:g:e := by euclid_finish
  have hs_dgb : Triangle.area △ d:g:b = Triangle.area △ b:g:d := by euclid_finish
  have hs_dfc : Triangle.area △ d:f:c = Triangle.area △ d:c:f := by euclid_finish
  have hs_cef : Triangle.area △ c:e:f = Triangle.area △ e:c:f := by euclid_finish
  have hs_adb : Triangle.area △ a:d:b = Triangle.area △ a:b:d := by euclid_finish
  linarith

end Elements.Book1
