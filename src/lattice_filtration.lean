import .lists

open lattice

/-- A filtration is a list of (not-strictly) increasing elements of the lattice -/
class filtration (α) [preorder α] := (modules : list α) (c : list.chain' (≤) modules)

namespace filtration
  def le_pair (α) [has_le α] := { p : α × α // p.1 ≤ p.2}
  
  instance (α) [preorder α]: has_coe (filtration α) (list α) := ⟨ λ F, F.modules ⟩

  def factors_up {α} [bounded_lattice α] : filtration α → list (le_pair α)
  | ⟨ [],        _ ⟩ := []
  | ⟨ [x],       _ ⟩ := [⟨(x, ⊤), by simp⟩]
  | ⟨ (x::y::l), h ⟩ := ⟨ (x, y) , list.chain'_of_first_two h⟩ ::
                      (factors_up ⟨ (y::l), (list.chain'_desc_left h)⟩)

  @[simp]
  def factors {α} [bounded_lattice α] : filtration α → list (le_pair α)
  | ⟨ [], _ ⟩ := [ ⟨ (⊥ , ⊤) , by simp ⟩ ]
  | ⟨ (x::l) , h ⟩ := ⟨ (⊥ , x), by simp ⟩ :: factors_up ⟨ (x::l) , h ⟩

  @[simp]
  lemma filtration_not_empty {α} [bounded_lattice α]:  Π (F : filtration α), F.factors ≠ []
  | ⟨ [], _ ⟩     := by simp
  | ⟨ (x::l), h ⟩ := by simp
end filtration