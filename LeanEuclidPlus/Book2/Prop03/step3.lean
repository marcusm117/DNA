import SystemE

namespace Elements.Book2

/- 2.3.3: AF drawn through A parallel to CD/BE [Prop.~1.31]. The line AF through a, parallel to
   CD, is produced by the proposition_31 construction in Main; this helper repackages its facts. -/
set_option systemE.solverTime 30 in
theorem helper_2_step3 (a : Point) (AF CD : Line)
    (haAF : a.onLine AF) (hAFCD : ¬(AF.intersectsLine CD)) :
    a.onLine AF ∧ ¬(AF.intersectsLine CD) := by
  exact ⟨haAF, hAFCD⟩

end Elements.Book2
