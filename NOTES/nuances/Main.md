# Book 2
## Prop 14
- signature is only for quadrilateral not any rectilinear. this is limitation of system E. Book 1 also had this (believe prop 45).

# Book 1
- we cannot formalize two tirangel sharing the same side since we do not have a triangle object that has a side property, so we write a tautology.
- ""and they are adjacent."
    (step9 : between d c e) := by sorry". I do not think this is faithful but I believe this is the best we can do with the currnet formal system.
### ex
  -- @assumption ("a straight-line stood on  a(nother) straight-line makes the adjacent angles equal to one another", ∠ d:c:f = ∠ e:c:f ∧ between d c e)
  euclid_sentence "1.11.10"
    "But when a straight-line stood on  a(nother) straight-line makes the adjacent angles equal to one another, each of the equal angles is a right-angle [Def.~1.10]."
    (step10 : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟) := by sorry

  euclid_sentence "1.11.11"
    "Thus, each of the (angles) $DCF$ and $FCE$ is a right-angle. "
    (step11 : ∠ d:c:f = ∟ ∧ ∠ f:c:e = ∟) := by sorry
this is redundant, but I would argue euclid repeating a def is redundant so this is actually faithful.