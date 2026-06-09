import SystemE
import Book.Prop30
import Book.Prop31
import Book.Prop46

namespace Elements.Book2

open Elements.Book1

/-! Step lemmas for Prop 2.2, one per Euclid sentence (faithful-euclid Phase B output).
    Each `helper_2_stepN` realizes sentence 2.2.N; the main proof in `Prop02.lean` discharges
    each `euclid_sentence` by `euclid_apply`ing the corresponding lemma. -/

/- 2.2.1 (construction): square ADEB on AB, CF through C parallel to AD/BE, f = CF ∩ DE.
   The crux `between d f e` follows from `between a c b` and the parallel verticals
   (CF ∥ AD given, CF ∥ BE via proposition_30). -/
set_option systemE.solverTime 30 in
theorem helper_2_step1 (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hab : distinctPointsOnLine a b AB) (hc : c.onLine AB) (hacb : between a c b)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hde : |(d─e)| = |(a─b)|) (had : |(a─d)| = |(a─b)|) (hbe : |(b─e)| = |(a─b)|)
    (hbad : ∠ b:a:d = ∟) (hade : ∠ a:d:e = ∟) (habe : ∠ a:b:e = ∟) (hbed : ∠ b:e:d = ∟)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hfDE : f.onLine DE) (hfCF : f.onLine CF) :
    |(a─d)| = |(a─b)| ∧ |(b─e)| = |(a─b)| ∧
    (∠ b:a:d = ∟) ∧ (∠ a:d:e = ∟) ∧ (∠ a:b:e = ∟) ∧
    c.onLine CF ∧ ¬(CF.intersectsLine AD) ∧
    f.onLine DE ∧ f.onLine CF ∧ between d f e := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_finish

/- 2.2.2: square AE = rectangles AF + CE. Area split of the square by C (on AB) and F (on DE). -/
set_option systemE.solverTime 30 in
theorem helper_2_step2 (a b c d e f : Point) (AB DE AD BE : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hdfe : between d f e) (hacb : between a c b) :
    Triangle.area △ d:a:b + Triangle.area △ d:b:e =
      (Triangle.area △ d:a:c + Triangle.area △ d:c:f)
    + (Triangle.area △ f:c:b + Triangle.area △ f:b:e) := by
  euclid_intros
  euclid_apply (sum_parallelograms_area d e a b f c DE AB AD BE)
  euclid_finish

/- 2.2.3: AE is the square on AB, area |a─b|·|a─b|. rectangle_area on the square. -/
set_option systemE.solverTime 30 in
theorem helper_2_step3 (a b d e : Point) (AB DE AD BE : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hde : |(d─e)| = |(a─b)|) (had : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟) :
    Triangle.area △ d:a:b + Triangle.area △ d:b:e = |(a─b)| * |(a─b)| := by
  euclid_intros
  euclid_apply (rectangle_area d e a b DE AB AD BE)
  have hda : |(d─a)| = |(a─b)| := by euclid_finish
  have hrw : |(a─b)| * |(a─b)| = |(d─e)| * |(d─a)| := by rw [hde, hda]
  rw [hrw]
  euclid_finish

/- 2.2.4: AF = rect(BA,AC). rectangle_area on the sub-rectangle a,c,f,d; |a─d| = |a─b| = |b─a|. -/
set_option systemE.solverTime 30 in
theorem helper_2_step4 (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (had : |(a─d)| = |(a─b)|) (hbad : ∠ b:a:d = ∟)
    (hcAB : c.onLine AB) (hacb : between a c b)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hfDE : f.onLine DE) (hfCF : f.onLine CF) (hdfe : between d f e) :
    Triangle.area △ d:a:c + Triangle.area △ d:c:f = |(b─a)| * |(a─c)| := by
  euclid_intros
  euclid_apply (rectangle_area a c d f AB DE AD CF)
  have hba : |(b─a)| = |(a─d)| := by euclid_finish
  have hprod : |(b─a)| * |(a─c)| = |(a─c)| * |(a─d)| := by rw [hba]; ring
  rw [hprod]
  euclid_finish

/- 2.2.5: CE = rect(AB,BC). rectangle_area on the sub-rectangle b,c,f,e; |b─e| = |a─b|. -/
set_option systemE.solverTime 30 in
theorem helper_2_step5 (a b c d e f : Point) (AB DE AD BE CF : Line)
    (hsq : formParallelogram d e a b DE AB AD BE)
    (hbe : |(b─e)| = |(a─b)|) (habe : ∠ a:b:e = ∟)
    (hcAB : c.onLine AB) (hacb : between a c b)
    (hcCF : c.onLine CF) (hCFAD : ¬(CF.intersectsLine AD))
    (hfDE : f.onLine DE) (hfCF : f.onLine CF) (hdfe : between d f e) :
    Triangle.area △ f:c:b + Triangle.area △ f:b:e = |(a─b)| * |(b─c)| := by
  euclid_intros
  euclid_apply (proposition_30 CF BE AD)
  euclid_apply (rectangle_area b c e f AB DE BE CF)
  have hab : |(a─b)| = |(b─e)| := by euclid_finish
  have hprod : |(a─b)| * |(b─c)| = |(b─e)| * |(b─c)| := by rw [hab]
  rw [hprod]
  euclid_finish

/- 2.2.6: rect(BA,AC) + rect(AB,BC) = square on AB. Substitution of steps 2–5. -/
set_option systemE.solverTime 30 in
theorem helper_2_step6 (a b c d e f : Point)
    (step2 : Triangle.area △ d:a:b + Triangle.area △ d:b:e =
             (Triangle.area △ d:a:c + Triangle.area △ d:c:f)
           + (Triangle.area △ f:c:b + Triangle.area △ f:b:e))
    (step3 : Triangle.area △ d:a:b + Triangle.area △ d:b:e = |(a─b)| * |(a─b)|)
    (step4 : Triangle.area △ d:a:c + Triangle.area △ d:c:f = |(b─a)| * |(a─c)|)
    (step5 : Triangle.area △ f:c:b + Triangle.area △ f:b:e = |(a─b)| * |(b─c)|) :
    |(b─a)| * |(a─c)| + |(a─b)| * |(b─c)| = |(a─b)| * |(a─b)| := by
  rw [← step3, step2, step4, step5]

end Elements.Book2
