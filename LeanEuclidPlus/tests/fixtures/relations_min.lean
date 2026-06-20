import SystemE.Theory.Sorts

opaque Point.onLine : Point → Line → Prop

@[simp]
abbrev distinctPointsOnLine : Point → Point → Line → Prop := λ P Q L => P.onLine L ∧ Q.onLine L ∧ P ≠ Q

opaque between : Point → Point → Point → Prop
