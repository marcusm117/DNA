import SystemE
import Book.Prop43
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

open Elements.Book1

/- 2.5.6 sub: proposition_43 complement equality on the square CEFB (diagonal B-E through h).
   prop43 corners (a b c d e f g h k) ↦ (b c e f d g l m h), lines (AD BC AB CD AC EF GH) ↦
   (BF CE AB EF BE DG KM): big square `b f c e`, diagonal BE through h, the two about-diagonal
   parallelograms BMDH (`b m d h`) and HGLE (`h g l e`). Yields △d:c:l + △d:l:h = △m:h:g + △m:g:f. -/
theorem helper_2_5_step6_compl (b c d e f g h l m : Point) (AB BE CE BF EF DG KM : Line)
    (hbBE : b.onLine BE) (heBE : e.onLine BE) (hhBE : h.onLine BE)
    (hbBF : b.onLine BF) (hecBF : e.sameSide c BF)
    (hbig : formParallelogram b f c e BF CE AB EF)
    (hbmf : between b m f)
    (hpar1 : formParallelogram b m d h BF DG AB KM)
    (hpar2 : formParallelogram h g l e DG CE KM EF) :
    Triangle.area △ d:c:l + Triangle.area △ d:l:h
      = Triangle.area △ m:h:g + Triangle.area △ m:g:f := by
  euclid_intros
  euclid_apply (proposition_43 b c e f d g l m h BF CE AB EF BE DG KM)
  euclid_finish

end Elements.Book2
