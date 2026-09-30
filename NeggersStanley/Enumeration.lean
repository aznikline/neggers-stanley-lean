import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Nodup
import Mathlib.Tactic

/-! Complete enumeration of linear extensions by repeatedly removing a minimum. -/

namespace NeggersStanley

def extensionWords {α : Type*} [DecidableEq α] (r : α → α → Prop)
    [DecidableRel r] : ℕ → List α → List (List α)
  | 0, pool => if pool = [] then [[]] else []
  | n+1, pool => if pool = [] then [[]] else
      pool.flatMap fun x => if ∀ y ∈ pool, ¬ r y x then
        (extensionWords r n (pool.erase x)).map (x :: ·) else []

theorem mem_extensionWords_iff {α : Type*} [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (hirr : ∀ x, ¬ r x x) :
    ∀ (n : ℕ) (pool l : List α), pool.length = n →
      (l ∈ extensionWords r n pool ↔
        l.Perm pool ∧ l.Pairwise (fun x y => ¬ r y x)) := by
  intro n
  induction n with
  | zero =>
    intro pool l hlen
    have hp : pool = [] := List.length_eq_zero_iff.mp hlen
    subst pool
    simp [extensionWords, List.perm_nil]
    intro h
    subst l
    simp
  | succ n ih =>
    intro pool l hlen
    have hne : pool ≠ [] := by intro h; simp [h] at hlen
    simp only [extensionWords, if_neg hne, List.mem_flatMap]
    constructor
    · rintro ⟨x, hx, hm⟩
      split_ifs at hm with hmin
      · obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hm
        have hlen' : (pool.erase x).length = n := by
          rw [List.length_erase_of_mem hx, hlen]; omega
        obtain ⟨hp, hpair⟩ := (ih _ _ hlen').mp ht
        refine ⟨(hp.cons x).trans (List.perm_cons_erase hx).symm, ?_⟩
        rw [List.pairwise_cons]
        exact ⟨fun y hy => hmin y (List.mem_of_mem_erase (hp.mem_iff.mp hy)), hpair⟩
      · simp at hm
    · rintro ⟨hp, hpair⟩
      cases l with
      | nil => exact False.elim (hne ((List.perm_nil.mp hp.symm)))
      | cons x tail =>
        have hx : x ∈ pool := hp.mem_iff.mp (by simp)
        have htail : tail.Perm (pool.erase x) :=
          (hp.trans (List.perm_cons_erase hx)).cons_inv
        have hmin : ∀ y ∈ pool, ¬ r y x := by
          intro y hy
          have hy' := hp.mem_iff.mpr hy
          rcases List.mem_cons.mp hy' with rfl | hy'
          · exact hirr _
          · exact (List.pairwise_cons.mp hpair).1 y hy'
        refine ⟨x, hx, ?_⟩
        rw [if_pos hmin]
        apply List.mem_map.mpr
        refine ⟨tail, ?_, rfl⟩
        have hlen' : (pool.erase x).length = n := by
          rw [List.length_erase_of_mem hx, hlen]; omega
        exact (ih _ _ hlen').mpr ⟨htail, (List.pairwise_cons.mp hpair).2⟩

theorem nodup_extensionWords {α : Type*} [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] :
    ∀ (n : ℕ) (pool : List α), pool.Nodup → (extensionWords r n pool).Nodup := by
  intro n
  induction n with
  | zero => intro pool hp; simp [extensionWords]; split_ifs <;> simp
  | succ n ih =>
    intro pool hp
    rw [extensionWords]
    split_ifs with he
    · simp
    · apply List.nodup_flatMap.mpr
      constructor
      · intro x hx
        split_ifs
        · exact (ih _ (hp.erase x)).map (fun a b h => (List.cons.inj h).2)
        · simp
      · apply hp.imp
        intro x y hxy
        change List.Disjoint (if ∀ z ∈ pool, ¬r z x then _ else [])
          (if ∀ z ∈ pool, ¬r z y then _ else [])
        split_ifs <;> try simp
        intro l hlx hly
        obtain ⟨xs, _, rfl⟩ := List.mem_map.mp hlx
        obtain ⟨ys, _, heq⟩ := List.mem_map.mp hly
        exact hxy (List.cons.inj heq).1.symm

/-- The efficient enumeration has exactly the same words, each once,
as filtering all permutations by the linear-extension condition. -/
theorem extensionWords_perm_filter {α : Type*} [DecidableEq α]
    (r : α → α → Prop) [DecidableRel r] (hirr : ∀ x, ¬r x x)
    (pool : List α) (hp : pool.Nodup) :
    (extensionWords r pool.length pool).Perm
      (pool.permutations.filter fun l => decide (l.Pairwise (fun x y => ¬r y x))) := by
  apply (List.perm_ext_iff_of_nodup (nodup_extensionWords r _ _ hp)
    ((List.nodup_permutations pool hp).filter _)).mpr
  intro l
  rw [mem_extensionWords_iff r hirr _ _ _ rfl]
  simp only [List.mem_filter, List.mem_permutations, decide_eq_true_eq]

#print axioms mem_extensionWords_iff
#print axioms nodup_extensionWords
#print axioms extensionWords_perm_filter

end NeggersStanley
