import NeggersStanley.Enumeration
import Mathlib.Algebra.Polynomial.Coeff

set_option autoImplicit false

namespace NeggersStanley

open Polynomial

/-- A strict partial order on the explicitly labelled set `0,...,n-1`.
The labels are translated by one when compared with the published source. -/
structure LabeledPoset (n : ℕ) where
  lt : Fin n → Fin n → Bool
  irrefl : ∀ i, lt i i = false
  trans : ∀ i j k, lt i j = true → lt j k = true → lt i k = true

def LabeledPoset.rel {n : ℕ} (P : LabeledPoset n) (i j : Fin n) : Prop :=
  P.lt i j = true

instance {n : ℕ} (P : LabeledPoset n) : DecidableRel P.rel :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

def LabeledPoset.NaturallyLabeled {n : ℕ} (P : LabeledPoset n) : Prop :=
  ∀ i j, P.rel i j → i < j

def LabeledPoset.toPartialOrder {n : ℕ} (P : LabeledPoset n) : PartialOrder (Fin n) where
  le i j := i = j ∨ P.rel i j
  lt := P.rel
  lt_iff_le_not_ge i j := by
    constructor
    · intro hij
      refine ⟨Or.inr hij, ?_⟩
      rintro (heq | hji)
      · subst j
        simp [LabeledPoset.rel, P.irrefl] at hij
      · have h := P.trans i j i hij hji
        rw [P.irrefl] at h
        contradiction
    · rintro ⟨hij, hji⟩
      rcases hij with heq | h
      · exact False.elim (hji (Or.inl heq.symm))
      · exact h
  le_refl i := Or.inl rfl
  le_trans i j k hij hjk := by
    rcases hij with rfl | hij
    · exact hjk
    rcases hjk with rfl | hjk
    · exact Or.inr hij
    exact Or.inr (P.trans i j k hij hjk)
  le_antisymm i j hij hji := by
    rcases hij with h | hij
    · exact h
    rcases hji with h | hji
    · exact h.symm
    have h := P.trans i j i hij hji
    rw [P.irrefl] at h
    contradiction

def descents {n : ℕ} : List (Fin n) → ℕ
  | a :: b :: rest => (if b < a then 1 else 0) + descents (b :: rest)
  | _ => 0

theorem descents_cons_le_length {n : ℕ} (rest : List (Fin n)) :
    ∀ a, descents (a :: rest) ≤ rest.length := by
  induction rest with
  | nil => intro a; simp [descents]
  | cons b rest ih =>
    intro a
    have h := ih b
    simp only [descents, List.length_cons]
    split_ifs <;> omega

def linearExtensionWords {n : ℕ} (P : LabeledPoset n) : List (List (Fin n)) :=
  (List.finRange n).permutations.filter fun l =>
    decide (l.Pairwise fun a b => ¬ P.rel b a)

/-- The sum is over every permutation that respects the given partial
order. The exponent is one plus the number of ordinary label descents. -/
noncomputable def descentPolynomial {n : ℕ} (P : LabeledPoset n) : ℝ[X] :=
  ((linearExtensionWords P).map fun l => (X : ℝ[X]) ^ (1 + descents l)).sum

def enumWords {n : ℕ} (P : LabeledPoset n) : List (List (Fin n)) :=
  extensionWords P.rel n (List.finRange n)

theorem enumWords_perm {n : ℕ} (P : LabeledPoset n) :
    (enumWords P).Perm (linearExtensionWords P) := by
  simpa only [enumWords, linearExtensionWords, List.length_finRange] using
    extensionWords_perm_filter P.rel (fun i => by simp [LabeledPoset.rel, P.irrefl])
      (List.finRange n) (List.nodup_finRange n)

theorem enumWords_length {n : ℕ} (P : LabeledPoset n)
    (l : List (Fin n)) (hl : l ∈ enumWords P) : l.length = n := by
  have h := (mem_extensionWords_iff P.rel
    (fun i => by simp [LabeledPoset.rel, P.irrefl]) n _ l List.length_finRange).mp hl
  simpa using h.1.length_eq

def descentCounts {n : ℕ} (P : LabeledPoset n) : List ℕ :=
  (List.range (n+2)).map fun k =>
    (enumWords P).countP fun l => decide (1 + descents l = k)

theorem descentPolynomial_coeff {n : ℕ} (P : LabeledPoset n) (k : ℕ) :
    (descentPolynomial P).coeff k =
      ((enumWords P).countP (fun l => decide (1 + descents l = k)) : ℝ) := by
  have heq : descentPolynomial P =
      ((enumWords P).map fun l => (X : ℝ[X]) ^ (1 + descents l)).sum :=
    (((enumWords_perm P).map _).sum_eq).symm
  rw [heq]
  generalize enumWords P = words
  induction words with
  | nil => simp
  | cons l words ih =>
    simp only [List.map_cons, List.sum_cons, coeff_add, coeff_X_pow,
      List.countP_cons, Nat.cast_add, ih]
    split_ifs <;> simp_all [add_comm]

theorem descentPolynomial_coeff_eq_zero {n : ℕ} (P : LabeledPoset n)
    (hn : 0 < n) {k : ℕ} (hk : n < k) : (descentPolynomial P).coeff k = 0 := by
  rw [descentPolynomial_coeff]
  suffices (enumWords P).countP (fun l => decide (1 + descents l = k)) = 0 by simp [this]
  apply List.countP_eq_zero.mpr
  intro l hl
  have hlen := enumWords_length P l hl
  have hne : l ≠ [] := by intro h; simp [h] at hlen; omega
  cases l with
  | nil => contradiction
  | cons a rest =>
    have hd := descents_cons_le_length rest a
    simp only [List.length_cons] at hlen
    simp_all only [decide_eq_false_iff_not, decide_eq_true_eq]
    omega

end NeggersStanley
