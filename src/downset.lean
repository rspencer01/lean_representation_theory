import data.set
import data.set.lattice
import order.lattice

import .subsets

open classical

@[simp]
def downset (α : Type) [partial_order α] := {S : set α | ∀ (a : S) (b : α), b ≤ a → b ∈ S}

variables {α : Type} [partial_order α]

@[simp]
lemma empty_is_downset : ∅ ∈ downset α := by simp

@[simp]
lemma full_set_is_downset : (⊤ : set α) ∈ downset α :=
  (by simp; intros; trivial)

@[simp]
def down_closure : α → set α := λ a, {b | b ≤ a}

lemma lower_downset (a : downset α) (x : a) (y : α) : y ≤ x → y ∈ (a : set α) :=
begin
  intro h₁,
  exact a.property x y h₁
end

lemma down_closure_is_downset (a : α) : down_closure a ∈ downset α :=
begin
  simp,
  intros,
  rw set.mem_set_of_eq,
  transitivity;
  assumption
end

@[simp]
lemma intersections_of_downsets_are_downsets (a b : downset α) : (a : set α) ∩ b ∈ downset α :=
begin
  intros,
  dunfold downset,
  simp,
  intros,
  simp,
  have h_1 : b_1 ∈ (a : set α) := lower_downset a ⟨ x, set.mem_of_mem_inter_left h ⟩ b_1 a_1,
  have h_2 : b_1 ∈ (b : set α) := lower_downset b ⟨ x, set.mem_of_mem_inter_right h ⟩ b_1 a_1,
  exact ⟨ h_1 , h_2 ⟩
end

@[simp]
lemma union_of_downsets_are_downsets (a b : downset α) : (a : set α) ∪ b ∈ downset α :=
begin
  intros,
  dunfold downset,
  intros x y h₁,
  simp,
  have h₂ : x.val ∈ (a : set α) ∨ x.val ∈ (b : set α) := @set.mem_or_mem_of_mem_union α x a b x.property,
  cases h₂,
  exact or.inl (lower_downset a ⟨x, h₂ ⟩ y h₁),
  exact or.inr (lower_downset b ⟨x, h₂ ⟩ y h₁)
end
instance bounded_lattice_of_downset : lattice.bounded_lattice (downset α) := 
  s_complete_lattice (downset α) (intersections_of_downsets_are_downsets) (union_of_downsets_are_downsets) (empty_is_downset) (full_set_is_downset)