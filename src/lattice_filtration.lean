import order.order_iso
import .lists

open lattice

/-- A filtration is a list of (not-strictly) increasing elements of the lattice -/
structure filtration (α) [preorder α] := (modules : list α) (c : list.chain' (≤) modules)

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
  lemma factors_not_empty {α} [bounded_lattice α]:  Π (F : filtration α), F.factors ≠ []
  | ⟨ [], _ ⟩     := by simp
  | ⟨ (x::l), h ⟩ := by simp

  def map {α} {β} [preorder α] [preorder β] (f : ((≤) : α → α → Prop) ≃o ((≤) : β → β → Prop)) : 
    filtration α → filtration β := λ F, {
      modules := list.map f F.modules,
      c := list.chain'_map_of_chain' f (λ a b, iff.elim_left (@order_iso.ord _ _ _ _ f a b)) F.c
    }
  
  
  def descend {α} [q : preorder α] (F : filtration α) (h : F.modules ≠ []) : list {x : α // x ≤ F.modules.last h} := 
    (list.map₄ (λ x, x ≤ F.modules.last h) F.modules (λ a h2, (
      @list.chain'_trans_last _ (≤) F.modules q.le_refl q.le_trans F.c h a h2 )))

  def pop_back'' {α} [preorder α] (F : filtration α) (h : F.modules ≠ []) :
    filtration {x // x ≤ F.modules.last h} := {
    modules := descend F h,
    c := begin
      intros,
      cases F,
      cases F_modules,
      exact absurd rfl h,
      unfold descend,
      exact list.chain'_map₄ _ (F_modules_hd :: F_modules_tl) _ F_c
    end
  }
      
  def pop_back' {α} [preorder α] (F : filtration α) (h : F.modules ≠ []) :
    filtration α := {
    modules := list.init F.modules,
    c := list.chain'_init _ F.c
  }

  def pop_back {α} [preorder α] (F : filtration α) (h : F.modules ≠ []) :
    filtration {x // x ≤ F.modules.last h} := pop_back' (pop_back'' F h) (by cases F; cases F_modules; contradiction; finish)
 
end filtration
