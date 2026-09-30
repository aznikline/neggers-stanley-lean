import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-! A purely algebraic certificate for a nonreal polynomial root. -/

namespace NeggersStanley

open Polynomial

noncomputable def laguerre (p : ℝ[X]) (x : ℝ) : ℝ :=
  p.derivative.eval x ^ 2 - p.eval x * p.derivative.derivative.eval x

lemma laguerre_mul (p q : ℝ[X]) (x : ℝ) :
    laguerre (p*q) x = q.eval x ^ 2 * laguerre p x +
      p.eval x ^ 2 * laguerre q x := by
  simp only [laguerre, derivative_mul, derivative_add, eval_add, eval_mul]
  ring

lemma laguerre_nonneg_of_splits (p : ℝ[X]) (hp : p.Splits) (x : ℝ) :
    0 ≤ laguerre p x := by
  have hprod : ∀ s : Multiset ℝ, 0 ≤ laguerre ((s.map fun r => X - C r).prod) x := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp [laguerre]
    | @cons r s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, laguerre_mul]
      have hlin : laguerre (X - C r) x = 1 := by simp [laguerre]
      rw [hlin]
      positivity
  rw [hp.eq_prod_roots, laguerre_mul]
  have hconst : laguerre (C p.leadingCoeff) x = 0 := by simp [laguerre]
  rw [hconst]
  have h := hprod p.roots
  positivity

/-- A negative Laguerre value certifies an actual nonreal complex zero. -/
theorem exists_nonreal_root_of_laguerre_neg (p : ℝ[X]) (x : ℝ)
    (hneg : laguerre p x < 0) :
    ∃ z : ℂ, (p.map (algebraMap ℝ ℂ)).IsRoot z ∧ z.im ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hp : p.Splits := by
    apply (IsAlgClosed.splits (p.map (algebraMap ℝ ℂ))).of_splits_map
    intro z hz
    have hr : (p.map (algebraMap ℝ ℂ)).IsRoot z :=
      (mem_roots (by
        intro hp0
        have hp0' : p = 0 := (Polynomial.map_eq_zero_iff (algebraMap ℝ ℂ).injective).mp hp0
        subst p
        simp [laguerre] at hneg)).mp hz
    refine ⟨z.re, ?_⟩
    exact Complex.ext (by simp) (by simpa using (h z hr).symm)
  exact (not_lt_of_ge (laguerre_nonneg_of_splits p hp x)) hneg

#print axioms exists_nonreal_root_of_laguerre_neg

end NeggersStanley
