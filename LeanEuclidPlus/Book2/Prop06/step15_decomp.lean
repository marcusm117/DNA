import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.6.15 sub: gnomon NOP + (square) LG = whole square CEFD (△c:e:f + △c:f:d). Two cuts:
   (a) the square CEFD (formParallelogram c e d f CE DF AB EF) cut by KM at l (on CE) and m (on DF)
       splits into the top strip CDML and the bottom strip LMFE (sum_parallelograms_area);
   (b) the bottom strip LMFE (formParallelogram l m e f KM EF CE DF) cut by BG at h (on KM) and g
       (on EF) splits into the corner LHGE and the rectangle HMFG (sum_parallelograms_area).
   Adding: (CDML) + (HMFG) + (LHGE) = (CDML) + (LMFE) = square. euclid_finish reconciles the
   triangulations. -/
theorem helper_2_6_step15_decomp (c d e f g h l m : Point) (AB CE DF EF KM BG : Line)
    (hsqpar : formParallelogram c e d f CE DF AB EF)
    (hbotpar : formParallelogram l m e f KM EF CE DF)
    (hcle : between c l e) (hdmf : between d m f)
    (hlhm : between l h m) (hegf : between e g f) :
    ((Triangle.area △ c:d:m + Triangle.area △ c:m:l) +
        (Triangle.area △ h:m:f + Triangle.area △ h:f:g)) +
      (Triangle.area △ l:h:g + Triangle.area △ l:g:e) =
      Triangle.area △ c:e:f + Triangle.area △ c:f:d := by
  euclid_intros
  euclid_apply (sum_parallelograms_area c e d f l m CE DF AB EF)
  euclid_apply (sum_parallelograms_area l m e f h g KM EF CE DF)
  euclid_finish

end Elements.Book2
