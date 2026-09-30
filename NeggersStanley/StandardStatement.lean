import NeggersStanley.Main

set_option autoImplicit false

namespace NeggersStanley

open Polynomial

/-- The convention with exponent exactly the number of descents. -/
noncomputable def eulerianPolynomial {n : ℕ} (P : LabeledPoset n) : ℝ[X] :=
  ((linearExtensionWords P).map fun l => (X : ℝ[X]) ^ descents l).sum

theorem descentPolynomial_eq_X_mul {n : ℕ} (P : LabeledPoset n) :
    descentPolynomial P = X * eulerianPolynomial P := by
  unfold descentPolynomial eulerianPolynomial
  generalize linearExtensionWords P = words
  induction words with
  | nil => simp
  | cons l words ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, pow_add, pow_one, mul_add]

theorem witness_eulerian_nonreal :
    ∃ z : ℂ, ((eulerianPolynomial witness).map (algebraMap ℝ ℂ)).IsRoot z ∧ z.im ≠ 0 := by
  obtain ⟨z, hz, hi⟩ := exists_nonreal_root_of_laguerre_neg
    (descentPolynomial witness) (-2) (by rw [witness_laguerre_value]; norm_num)
  have hnz : z ≠ 0 := by intro h; simp [h] at hi
  rw [descentPolynomial_eq_X_mul] at hz
  have hm : z * ((eulerianPolynomial witness).map (algebraMap ℝ ℂ)).eval z = 0 := by
    simpa only [IsRoot.def, Polynomial.map_mul, Polynomial.map_X, eval_mul, eval_X] using hz
  exact ⟨z, (mul_eq_zero.mp hm).resolve_left hnz, hi⟩

/-- A semantic definition using Mathlib's actual partial-order structure,
independent of the executable certificate representation. -/
noncomputable def posetEulerianPolynomial {n : ℕ} (P : PartialOrder (Fin n)) : ℝ[X] := by
  classical
  exact (((List.finRange n).permutations.filter fun l =>
    decide (l.Pairwise fun a b => ¬P.lt b a)).map fun l => (X : ℝ[X]) ^ descents l).sum

theorem posetEulerian_toPartialOrder {n : ℕ} (P : LabeledPoset n) :
    posetEulerianPolynomial P.toPartialOrder = eulerianPolynomial P := by
  classical
  unfold posetEulerianPolynomial eulerianPolynomial linearExtensionWords
  congr 2
  apply List.filter_congr
  intro l hl
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rfl

/-- Full counterexample with a standard partial order and the unshifted
descent generating polynomial. There are no additional proof premises. -/
theorem exists_naturally_labeled_poset_with_nonreal_zero :
    ∃ P : PartialOrder (Fin 17),
      (∀ i j : Fin 17, P.lt i j → i.val < j.val) ∧
      ∃ z : ℂ, ((posetEulerianPolynomial P).map (algebraMap ℝ ℂ)).IsRoot z ∧ z.im ≠ 0 := by
  refine ⟨witness.toPartialOrder, witness_naturally_labeled, ?_⟩
  rw [posetEulerian_toPartialOrder]
  exact witness_eulerian_nonreal

theorem witness_linear_extension_count : (linearExtensionWords witness).length = 7016 := by
  have h := congrArg (fun p : ℝ[X] => p.eval 1) witness_polynomial
  have heval : (descentPolynomial witness).eval 1 =
      ((linearExtensionWords witness).length : ℝ) := by
    simp [descentPolynomial, eval_listSum, List.map_map, Function.comp_def]
  rw [heval] at h
  norm_num [witnessPolynomial] at h
  exact_mod_cast h

#print axioms exists_naturally_labeled_poset_with_nonreal_zero
#print axioms witness_linear_extension_count

end NeggersStanley
