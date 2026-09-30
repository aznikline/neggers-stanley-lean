import NeggersStanley.Witness

set_option autoImplicit false

namespace NeggersStanley

open Polynomial

noncomputable def witnessPolynomial : ℝ[X] :=
  X + C 32 * X^2 + C 336 * X^3 + C 1420 * X^4 +
  C 2534 * X^5 + C 1946 * X^6 + C 658 * X^7 + C 86 * X^8 + C 3 * X^9

theorem witness_polynomial : descentPolynomial witness = witnessPolynomial := by
  ext k
  by_cases hk : k ≤ 17
  · have h := congrArg (fun l : List ℕ => l[k]?) witness_counts
    rw [descentCounts, List.getElem?_map,
      List.getElem?_range (by omega : k < 17+2), Option.map_some] at h
    rw [descentPolynomial_coeff]
    interval_cases k
    all_goals simp only [List.getElem?_cons_zero, List.getElem?_cons_succ] at h
    all_goals rw [Option.some.inj h]
    all_goals norm_num [witnessPolynomial, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X]
  · rw [descentPolynomial_coeff_eq_zero witness (by decide) (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    have hd : witnessPolynomial.natDegree ≤ 9 := by
      unfold witnessPolynomial
      compute_degree
    omega

theorem witness_laguerre_value : laguerre (descentPolynomial witness) (-2) = -18495 := by
  rw [witness_polynomial]
  norm_num [laguerre, witnessPolynomial, derivative_add, derivative_mul, derivative_pow]

/-- A naturally labelled partial order on seventeen elements whose
actual linear-extension descent polynomial has a nonreal complex zero. -/
theorem neggers_stanley_counterexample :
    ∃ P : LabeledPoset 17, P.NaturallyLabeled ∧
      ∃ z : ℂ, ((descentPolynomial P).map (algebraMap ℝ ℂ)).IsRoot z ∧ z.im ≠ 0 := by
  refine ⟨witness, witness_naturally_labeled, ?_⟩
  apply exists_nonreal_root_of_laguerre_neg (descentPolynomial witness) (-2)
  rw [witness_laguerre_value]
  norm_num

def NeggersConjecture : Prop :=
  ∀ (n : ℕ) (P : LabeledPoset n), P.NaturallyLabeled →
    ∀ z : ℂ, ((descentPolynomial P).map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0

theorem not_neggersConjecture : ¬ NeggersConjecture := by
  intro h
  obtain ⟨P, hP, z, hz, hnr⟩ := neggers_stanley_counterexample
  exact hnr (h 17 P hP z hz)

#print axioms witness_polynomial
#print axioms witness_laguerre_value
#print axioms neggers_stanley_counterexample
#print axioms not_neggersConjecture

end NeggersStanley
