import Mathlib.SetTheory.ZFC.Basic
import MIL.Common

section
open ZFSet

theorem pair_to_singleton {s : ZFSet} : ({s, s} : ZFSet) = {s} := by
  ext x
  rw [mem_pair, mem_singleton]
  constructor
  rintro (xs | xs)
  exact xs
  exact xs
  apply Or.inl

theorem singleton_eq {a b : ZFSet} (h : ({a} : ZFSet) = {b}) : a = b := by
  rw [← mem_singleton]
  rw [← ext_iff.1 h a]
  rw [mem_singleton]

theorem pair_comm {a b : ZFSet} : ({a, b} : ZFSet) = {b, a} := by
  rw [ext_iff]
  intro x
  rw [mem_pair, mem_pair]
  apply Or.comm

theorem pair_eq {a b c d : ZFSet} (h1 : ({a, b} : ZFSet) = {c, d}) (h2: a = c) : b = d := by
  rw [h2] at h1
  by_cases h3: b = c
  · rw [h3, pair_to_singleton] at h1
    symm
    rw [h3, ← mem_singleton, h1, mem_pair]
    right
    rfl
  have h4: b ∈ {c, d} := by
    rw [← h1, mem_pair]
    right
    rfl
  rw [mem_pair] at h4
  rcases h4 with h4 | h4
  · exfalso
    apply h3 h4
  exact h4

theorem pair_eq2 {a b c d : ZFSet} (h1 : ({a, b} : ZFSet) = {c, d}) (h2: a ≠ c) : a = d ∧ b = c := by
  constructor
  have h3: a ∈ {c, d} := by
    rw [← h1, mem_pair]
    left
    rfl
  rw [mem_pair] at h3
  rcases h3 with h3 | h3
  · exfalso
    apply h2 h3
  exact h3
  have h4 : c ∈ {a, b} := by
    rw [h1, mem_pair]
    left
    rfl
  rw [mem_pair] at h4
  rcases h4 with h4 | h4
  · symm at h4
    exfalso
    apply h2 h4
  symm
  exact h4

theorem ordered_pair_eq {a b c d : ZFSet} : ({{a}, {a, b}} : ZFSet) = {{c}, {c, d}} ↔ a = c ∧ b = d := by
  constructor
  · by_cases h1 : a = c
    · rw [h1]
      intro h2
      constructor
      · rfl
      have h3 : {c, b} = {c, d} := by
        apply pair_eq h2 rfl
      apply pair_eq h3 rfl
    intro h2
    have h3 : ¬ {a} = {c} := by
      intro h3
      apply h1
      apply singleton_eq h3
    apply pair_eq2 h2 at h3
    have h4: a = c := by
      rw [← mem_singleton, ← h3.right, mem_pair]
      left
      rfl
    exfalso
    apply h1 h4
  rintro ⟨h1, h2⟩
  rw [h1, h2]

theorem powerset_not_subset {x : ZFSet} : ¬ powerset x ⊆ x := by
  rintro h
  let sz := ZFSet.sep (fun (z : ZFSet) ↦ z ∉ z) x
  have h2 : sz ∈ x := by
    apply h
    rw [mem_powerset]
    intro z hz
    rw [mem_sep] at hz
    exact hz.left
  by_cases h3: sz ∈ sz
  · have h4: sz ∉ sz := by
      rw [mem_sep] at h3
      exact h3.right
    contradiction
  have h4: sz ∈ sz := by
    rw [mem_sep]
    exact ⟨h2, h3⟩
  contradiction

/--
inductive S ↔ (∅ ∈ S ∧ ∀ x ∈ S, x ∪ {x} ∈ S)
transitive S ↔ ∀ x ∈ S, x ⊆ S
-/

def inductiveSet (S : ZFSet) : Prop := ∅ ∈ S ∧ ∀ x ∈ S, x ∪ {x} ∈ S
def transitiveSet (S : ZFSet) : Prop := ∀ x, x ∈ S → x ⊆ S

theorem inductiveSet_sep {X : ZFSet} (h1 : inductiveSet X) : inductiveSet (ZFSet.sep (fun (x: ZFSet) ↦ x ⊆ X) X) := by
  obtain ⟨h1l, h1r⟩ := h1
  constructor
  · rw [mem_sep]
    constructor
    · exact h1l
    exact empty_subset X
  intro x
  rw [mem_sep, mem_sep]
  rintro ⟨h2, h3⟩
  constructor
  · apply h1r x h2
  rintro z hz
  rw [mem_union] at hz
  rcases hz with hz1 | hz2
  · exact h3 hz1
  rw [mem_singleton] at hz2
  rw [hz2]
  exact h2

theorem inductive_of_inter_of_emptyset{X Y : ZFSet} (h1: inductiveSet X) (h2: inductiveSet Y) : inductiveSet (X ∩ Y) := by
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  constructor
  · rw [mem_inter]
    exact ⟨h1l, h2l⟩
  rintro x
  rw [mem_inter, mem_inter]
  rintro ⟨xX, xY⟩
  exact ⟨h1r _ xX, h2r _ xY⟩

theorem inductive_omega : inductiveSet ZFSet.omega := by
  constructor
  · exact ZFSet.omega_zero
  intro n hn
  apply ZFSet.omega_succ at hn
  have h : n ∪ {n} = insert n n := by
    ext x
    rw [ZFSet.mem_insert_iff, ZFSet.mem_union, mem_singleton, Or.comm]
  rw [h]
  exact hn

-- Infinity 保证至少存在一个inductiveSet
-- Separation Schema 保证所有inductiveSet的交集是一个集合
-- 证明：所有inductiveSet的交集是一个inductiveSet
def sInter_of_all_inductiveSet := ZFSet.sep (fun x ↦ ∀ X, inductiveSet X → x ∈ X) ZFSet.omega
#check sInter_of_all_inductiveSet
theorem inductive_of_inter_of_inductiveSet : inductiveSet sInter_of_all_inductiveSet := by
  unfold sInter_of_all_inductiveSet
  constructor
  · rw [mem_sep]
    constructor
    · apply ZFSet.omega_zero
    intro X hX
    exact hX.left
  intro x hx
  rw [mem_sep]
  rw [mem_sep] at hx
  constructor
  · apply inductive_omega.right
    exact hx.left
  intro X hX
  obtain h3 := hx.right _ hX
  apply hX.right _ h3

theorem setin_not_comm{a b : ZFSet} : ¬ (a ∈ b ∧ b ∈ a) := by
  by_contra h1
  obtain ⟨h1l, h1r⟩ := h1
  have h2: ∃ x ∈ ({a, b} : ZFSet), {a, b} ∩ x = ∅ := by
    apply regularity
    by_contra h
    rw [eq_empty] at h
    apply h a
    rw [mem_pair]
    left
    rfl
  have h3: b ∈ {a, b} ∩ a := by
    rw [mem_inter, mem_pair]
    exact ⟨(Or.inr rfl), h1r⟩
  have h4: a ∈ {a, b} ∩ b := by
    rw [mem_inter, mem_pair]
    exact ⟨(Or.inl rfl), h1l⟩
  rcases h2 with ⟨x, hx, xinter⟩
  rw [mem_pair] at hx
  rcases hx with (hx | hx)
  · rw [hx, eq_empty] at xinter
    apply xinter b h3
  rw [hx, eq_empty] at xinter
  apply xinter a h4

end
