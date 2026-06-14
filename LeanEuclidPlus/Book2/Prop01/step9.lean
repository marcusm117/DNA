import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book2

/- 2.1.9: rectangle EH (= E,C,H,L) is the rectangle contained by A and EC.
   rectangle_area on the parallelogram e,l,c,h (right angle ∠e:c:h = ∟) gives
   △e:c:h + △e:l:h = |e─l| * |e─c|. The vertical side |e─l| equals |b─g| (opposite sides of the
   parallelogram BGLE, proposition_34) which equals |a₁a₂| (step2); so the area is |a₁a₂| * |e─c|.
   sub-nodes: step9_rangle (∠e:c:h = ∟), step9_pgram (the ELCH parallelogram), step9_len (|e─l| = |a₁a₂|). -/
set_option systemE.solverTime 30 in
theorem helper_2_1_step9 (a₁ a₂ b c d e f f' g h l : Point) (BC BF EL CH GH : Line)
    (hbBC : b.onLine BC) (hcBC : c.onLine BC) (hdBC : d.onLine BC) (heBC : e.onLine BC)
    (hbde : between b d e) (hdec : between d e c)
    (hbBF : b.onLine BF) (hfBF : f.onLine BF) (hfoffBC : ¬(f.onLine BC))
    (hf'BF : f'.onLine BF) (hbff' : between b f f') (hbgf' : between b g f')
    (hfbc : ∠ f:b:c = ∟) (hbg : |(b─g)| = |(a₁─a₂)|)
    (hgGH : g.onLine GH) (hGHBC : ¬(GH.intersectsLine BC))
    (heEL : e.onLine EL) (hlEL : l.onLine EL) (hELBF : ¬(EL.intersectsLine BF))
    (hcCH : c.onLine CH) (hhCH : h.onLine CH) (hCHBF : ¬(CH.intersectsLine BF))
    (hlGH : l.onLine GH) (hhGH : h.onLine GH) :
    Triangle.area △ e:c:h + Triangle.area △ e:l:h = |(a₁─a₂)| * |(e─c)| := by
  euclid_intros
  have hgoffBC : ¬(g.onLine BC) := by
    euclid_apply (between_same_line_in b g f' BF)
    euclid_finish
  have hloffBC : ¬(l.onLine BC) := by euclid_finish
  have hhoffBC : ¬(h.onLine BC) := by euclid_finish
  have step9_rangle : ∠ e:c:h = ∟ := by sorry
  have step9_pgram : formParallelogram e l c h EL CH BC GH := by sorry
  have step9_len : |(e─l)| = |(a₁─a₂)| := by sorry
  euclid_apply (rectangle_area e l c h EL CH BC GH)
  euclid_finish

end Elements.Book2
