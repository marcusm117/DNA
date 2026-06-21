import SystemE
import Book.Prop43
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.6.7 sub: proposition_43 complement equality on the square CEFD (diagonal D-E through h).
   prop43 corners (a b c d e f g h k) ↦ (d c e f b g l m h), lines (AD BC AB CD AC EF GH) ↦
   (DF CE AB EF DE BG KM): big square `d f c e`, diagonal DE through h, the two about-diagonal
   parallelograms DMBH (`d m b h`) and HGLE (`h g l e`). Yields △b:c:l + △b:l:h = △m:h:g + △m:g:f. -/
theorem helper_2_6_step7_compl (b c d e f g h l m : Point) (AB DE CE DF EF BG KM : Line)
    (hdDE : d.onLine DE) (heDE : e.onLine DE) (hhDE : h.onLine DE)
    (hdDF : d.onLine DF) (hecDF : e.sameSide c DF)
    (hbig : formParallelogram d f c e DF CE AB EF)
    (hdmf : between d m f)
    (hpar1 : formParallelogram d m b h DF BG AB KM)
    (hpar2 : formParallelogram h g l e BG CE KM EF) :
    Triangle.area △ b:c:l + Triangle.area △ b:l:h
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by
  euclid_intros
  euclid_apply (proposition_43 d c e f b g l m h DF CE AB EF DE BG KM)
  euclid_finish

end Elements.Book2
