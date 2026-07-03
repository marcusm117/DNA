import SystemE
import Mathlib.Tactic.Linarith
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_5_step11 (a b c d e f g : Point) (AB AC : Line)
    (haAB : a.onLine AB) (hbAB : b.onLine AB) (hfAB : f.onLine AB)
    (haAC : a.onLine AC) (hcAC : c.onLine AC)
    (habd : between a b d) (hbfd : between b f d)
    (hace : between a c e) (hage : between a g e)
    (hassump1 : |(a─f)| = |(a─g)|)
    (hassump2 : |(a─b)| = |(a─c)|) :
    |(b─f)| = |(c─g)| := by
  -- Derive g.onLine AC via transitivity (a,c on AC; between a c e → e on AC; between a g e → g on AC)
  have heAC : e.onLine AC := between_same_line_out a c e AC ⟨hace, haAC, hcAC⟩
  have hgAC : g.onLine AC := between_same_line_in a g e AC ⟨hage, haAC, heAC⟩
  -- between a b d ∧ between b f d → between a b f (order: A,B,F,D)
  have h_s1 := between_symm a b d habd
  have h_s2 := between_symm b f d hbfd
  have ha_ne_b : a ≠ b := h_s1.2.1
  have hb_ne_f : b ≠ f := h_s2.2.1
  -- between d f a: via between_trans_in on reversed order (D,B,A) ∧ (D,F,B)
  have hd_f_a : between d f a := between_trans_in d b a f ⟨h_s1.1, h_s2.1⟩
  have ha_f_d : between a f d := (between_symm d f a hd_f_a).1
  have ha_ne_f : a ≠ f := (between_symm a f d ha_f_d).2.1
  -- Now use between_points on A,B,F (all on AB) and eliminate the two bad cases
  have habf : between a b f := by
    rcases between_points a b f AB ⟨ha_ne_b, hb_ne_f, ha_ne_f.symm, haAB, hbAB, hfAB⟩
        with h | h | h
    · exact h
    · -- case between b a f: gives between b a d via between_trans_out, contradicts ¬between b a d
      exact absurd (between_trans_out b a f d ⟨h, ha_f_d⟩) h_s1.2.2.2
    · -- case between a f b: gives ¬between b f d via between_not_trans, contradicts hbfd
      exact absurd hbfd (between_not_trans a f b d ⟨h, ha_f_d⟩)
  have h_bf_eq := between_if a b f habf
  have h_bf_nn : 0 ≤ |(b─f)| := segment_gte_zero (b─f)
  -- between a c e ∧ between a g e → between a c g (order: A,C,G,E)
  have ha_ne_c : a ≠ c := (between_symm a c e hace).2.1
  have hg_ne_a : g ≠ a := (between_symm a g e hage).2.1.symm
  -- c ≠ g: if c=g then |a─c|=|a─g|, but |a─g|=|a─b|+|b─f|>|a─b|=|a─c|
  have hc_ne_g : c ≠ g := by
    intro hcg
    have heq : |(a─c)| = |(a─g)| := by rw [hcg]
    have h1 : |(b─f)| ≤ 0 := by linarith [hassump1, hassump2, h_bf_eq, heq]
    exact hb_ne_f (zero_segment_if b f (le_antisymm h1 h_bf_nn))
  have hacg : between a c g := by
    rcases between_points a c g AC ⟨ha_ne_c, hc_ne_g, hg_ne_a, haAC, hcAC, hgAC⟩
        with h | h | h
    · exact h
    · -- case between c a g: gives between c a e via between_trans_out, contradicts ¬between c a e
      exact absurd (between_trans_out c a g e ⟨h, hage⟩) (between_symm a c e hace).2.2.2
    · -- case between a g c: metric contradiction (|b─f|+|g─c|=0 but |b─f|>0)
      exfalso
      have h_gc_nn : 0 ≤ |(g─c)| := segment_gte_zero (g─c)
      have h1 : |(b─f)| ≤ 0 :=
        by linarith [hassump1, hassump2, h_bf_eq, between_if a g c h, h_gc_nn]
      exact hb_ne_f (zero_segment_if b f (le_antisymm h1 h_bf_nn))
  -- C.N.3: |b─f| = |a─f| - |a─b| = |a─g| - |a─c| = |c─g|
  linarith [hassump1, hassump2, h_bf_eq, between_if a c g hacg]

end Elements.Book1
