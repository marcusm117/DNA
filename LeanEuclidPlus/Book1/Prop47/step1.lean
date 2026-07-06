import SystemE
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace Elements.Book1

theorem helper_1_47_step1
    (b c d e : Point) (BC DE BD CE : Line)
    (a g f : Point) (AB GF AG BF : Line)
    (h k : Point) (AC HK AH CK : Line)
    (h_bd : |(b─d)| = |(b─c)|) (h_ce : |(c─e)| = |(b─c)|) (h_de : |(d─e)| = |(b─c)|)
    (h_cbd : (∠ c:b:d : ℝ) = ∟) (h_bde : (∠ b:d:e : ℝ) = ∟)
    (h_bce : (∠ b:c:e : ℝ) = ∟) (h_ced : (∠ c:e:d : ℝ) = ∟)
    (h_ag : |(a─g)| = |(a─b)|) (h_bf : |(b─f)| = |(a─b)|) (h_gf : |(g─f)| = |(a─b)|)
    (h_bag : (∠ b:a:g : ℝ) = ∟) (h_agf : (∠ a:g:f : ℝ) = ∟)
    (h_abf : (∠ a:b:f : ℝ) = ∟) (h_bfg : (∠ b:f:g : ℝ) = ∟)
    (h_ah : |(a─h)| = |(a─c)|) (h_ck : |(c─k)| = |(a─c)|) (h_hk : |(h─k)| = |(a─c)|)
    (h_cah : (∠ c:a:h : ℝ) = ∟) (h_ahk : (∠ a:h:k : ℝ) = ∟)
    (h_ack : (∠ a:c:k : ℝ) = ∟) (h_ckh : (∠ c:k:h : ℝ) = ∟) :
    (|(b─d)| = |(b─c)| ∧ |(c─e)| = |(b─c)| ∧ |(d─e)| = |(b─c)| ∧
        (∠ c:b:d = ∟) ∧ (∠ b:d:e = ∟) ∧ (∠ b:c:e = ∟) ∧ (∠ c:e:d = ∟)) ∧
      (|(a─g)| = |(a─b)| ∧ |(b─f)| = |(a─b)| ∧ |(g─f)| = |(a─b)| ∧
        (∠ b:a:g = ∟) ∧ (∠ a:g:f = ∟) ∧ (∠ a:b:f = ∟) ∧ (∠ b:f:g = ∟)) ∧
      (|(a─h)| = |(a─c)| ∧ |(c─k)| = |(a─c)| ∧ |(h─k)| = |(a─c)| ∧
        (∠ c:a:h = ∟) ∧ (∠ a:h:k = ∟) ∧ (∠ a:c:k = ∟) ∧ (∠ c:k:h = ∟)) :=
  ⟨⟨h_bd, h_ce, h_de, h_cbd, h_bde, h_bce, h_ced⟩,
   ⟨h_ag, h_bf, h_gf, h_bag, h_agf, h_abf, h_bfg⟩,
   ⟨h_ah, h_ck, h_hk, h_cah, h_ahk, h_ack, h_ckh⟩⟩

end Elements.Book1
