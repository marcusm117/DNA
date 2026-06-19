import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.5.6 sub: parallelogram BMDH = formParallelogram b m d h BF DG AB KM. (Mirror of Prop06 step7_par1
   under relabel d↔b, DF→BF, BG→DG.) sameSide a.sameSide c BD = b.sameSide d KM (step6_par1_ss);
   m ≠ h derived from m ∈ BF, ¬h ∈ BF? — here BD-slot distinctPointsOnLine m h KM... actually def
   a b c d AB CD AC BD: a=b,b=m on BF; c=d,d=h on DG; a=b,c=d on AB; b=m,d=h on KM. m ≠ h from the
   sameSide-bearing layout; passed/derived. Parallels BF∥DG, AB∥KM in hand. -/
/- formParallelogram b m d h BF DG AB KM. def a b c d AB CD AC BD: a=b,b=m on BF; c=d,d=h on DG;
   a=b,c=d on AB; b=m,d=h on KM. m ≠ h: from h ∉ BF (step6_hoffbf) and m ∈ BF. -/
theorem helper_2_5_step6_par1 (b d h m : Point) (BF DG AB KM : Line)
    (hbBF : b.onLine BF) (hmBF : m.onLine BF)
    (hdDG : d.onLine DG) (hhDG : h.onLine DG)
    (hbAB : b.onLine AB) (hdAB : d.onLine AB)
    (hmKM : m.onLine KM) (hhKM : h.onLine KM)
    (hhoffBF : ¬(h.onLine BF))
    (hssbd : b.sameSide d KM)
    (hDGBF : ¬(DG.intersectsLine BF)) (hKMAB : ¬(KM.intersectsLine AB)) :
    formParallelogram b m d h BF DG AB KM := by
  euclid_intros
  have hmh : m ≠ h := fun heq => hhoffBF (heq ▸ hmBF)
  refine ⟨hbBF, hmBF, hdDG, hhDG, hbAB, hdAB, ⟨hmKM, hhKM, hmh⟩, hssbd, ?_, ?_⟩
  · euclid_finish
  · euclid_finish

end Elements.Book2
