import Mathlib

open Filter Set
open scoped Topology



theorem thm_P
  (U : Set ℂ)
  (hU_1 : Nonempty U)
  (hU_2 : IsConnected U)
  (hU_3 : IsOpen U)
  (f_n : ℕ → ℂ → ℂ)
  (hf_n_1 : ∀ n : ℕ, DifferentiableOn ℂ (f_n n) U)
  (f : ℂ → ℂ)
  (hf_1 : ∀ X : Set ℂ, X ⊆ U ∧ IsCompact X → TendstoUniformlyOn (λ n x => f_n n x) f atTop X) :
  DifferentiableOn ℂ f U := by
  -- Obtain locally uniform convergence on `U` from uniform convergence on all compact subsets
  have hlu : TendstoLocallyUniformlyOn (fun n x => f_n n x) f atTop U := by
    -- Curry `hf_1` to match the lemma's expected shape
    have hf_1' : ∀ X : Set ℂ, X ⊆ U → IsCompact X →
        TendstoUniformlyOn (fun n x => f_n n x) f atTop X := by
      intro X hX hK; exact hf_1 X ⟨hX, hK⟩
    -- Use the characterization of locally uniform convergence on open sets
    simpa using
      (tendstoLocallyUniformlyOn_iff_forall_isCompact (α := ℂ) (β := ℂ)
          (F := fun n (x : ℂ) => f_n n x) (f := f) (p := atTop) (s := U) hU_3).2
        hf_1'
  -- The sequence functions are differentiable on `U` for all `n`, hence eventually
  have hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (fun x => f_n n x) U :=
    eventually_of_forall hf_n_1
  -- Apply the Weierstrass theorem for locally uniform limits of holomorphic functions
  exact hlu.differentiableOn hF hU_3



-- Proof of thm_Q using thm_P
theorem thm_Q (U : Set ℂ) (hU : IsOpen U)
  (hU1 : Nonempty U) (hU2 : IsConnected U) (f : ℕ → ℂ → ℂ) (f' : ℂ → ℂ)
  (hf : ∀ n : ℕ, DifferentiableOn ℂ (f n) U)
  (hf1 : ∀ X ⊆ U, CompactSpace X →
  (TendstoUniformly (λ n => restrict X (f n)) (restrict X f') atTop)) :
  DifferentiableOn ℂ f' U := by
  -- Apply `thm_P`, translating the hypothesis to the required form
  refine
    thm_P U hU1 hU2 hU f (by simpa using hf) f' ?_
  -- From uniform convergence on the subtype `X`, deduce uniform convergence on `X` as a set
  intro X hX
  have hsubset : X ⊆ U := hX.1
  have hcompact : IsCompact X := hX.2
  -- Equip the subtype `X` with a compact space structure from `IsCompact X`
  have _inst : CompactSpace X := isCompact_iff_compactSpace.mp hcompact
  -- Use the equivalence between `TendstoUniformlyOn` on a set and `TendstoUniformly` on the subtype
  have hTU : TendstoUniformly (fun n (x : X) => f n x) (fun x : X => f' x) atTop := by
    simpa using hf1 X hsubset _inst
  simpa [Function.comp] using
    (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).mpr hTU



-- Proof of thm_P using thm_Q
theorem thm_P'
  (U : Set ℂ)
  (hU_1 : Nonempty U)
  (hU_2 : IsConnected U)
  (hU_3 : IsOpen U)
  (f_n : ℕ → ℂ → ℂ)
  (hf_n_1 : ∀ n : ℕ, DifferentiableOn ℂ (f_n n) U)
  (f : ℂ → ℂ)
  (hf_1 : ∀ X : Set ℂ, X ⊆ U ∧ IsCompact X → TendstoUniformlyOn (λ n x => f_n n x) f atTop X) :
  DifferentiableOn ℂ f U := by
  -- Deduce `thm_P` from `thm_Q` by translating to a subtype-uniform convergence statement.
  refine thm_Q U hU_3 hU_1 hU_2 (fun n => f_n n) f (by simpa) ?_
  intro X hXsub hXcomp
  have hOn : TendstoUniformlyOn (fun n x => f_n n x) f atTop X :=
    hf_1 X ⟨hXsub, (isCompact_iff_compactSpace).mpr hXcomp⟩
  simpa using (tendstoUniformlyOn_iff_tendstoUniformly_comp_coe).mp hOn
