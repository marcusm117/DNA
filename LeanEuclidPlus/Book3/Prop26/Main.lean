import SystemE

namespace Elements.Book3

-- III.26: in equal circles, equal INSCRIBED angles (at the circumferences) stand on equal arcs.
-- Hypothesis: equal circles (|(g─b)| = |(h─e)|, i.e. equal radii) + equal inscribed angles ∠b:a:c = ∠e:d:f.
-- Goal: arc BKC = arc ELF, encoded (arc→central-angle convention) as ∠b:g:c = ∠e:h:f.
-- This is the non-trivial circumference case: ∠b:g:c = ∠e:h:f does NOT appear as a hypothesis.
-- (The former circular version had ∠b:g:c = ∠e:h:f as BOTH hypothesis AND goal — goal = assumption.)
-- Proof outline: inscribed angles equal ⟹ (via [III.20]) central angles equal ⟹ BG=GC=EH=HF + SAS ⟹
-- BC=EF; segment BAC ∼ segment EDF [Def.3.11] + [III.24] ⟹ segment BAC = segment EDF;
-- equal circles − equal segments ⟹ arc BKC = arc ELF.
theorem proposition_26 : ∀ (a b c d e f g h : Point) (ABC DEF : Circle),
  a.onCircle ABC ∧ b.onCircle ABC ∧ c.onCircle ABC ∧
  d.onCircle DEF ∧ e.onCircle DEF ∧ f.onCircle DEF ∧
  g.isCentre ABC ∧ h.isCentre DEF ∧
  |(g─b)| = |(h─e)| ∧
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f ∧
  ∠ b:a:c = ∠ e:d:f →
  ∠ b:g:c = ∠ e:h:f :=
by
  sorry
