import algebra.category.Module.basic
import .lattices

variables (R : Type) [ring R] {M : Module R}

def is_minimal {α : Type} [lattice.bounded_lattice α] (x : α) := x ≠ ⊥ ∧ ∀ y, y < x → y = ⊥ 

def inf_with_minimal_bot_or_idem {α : Type} [lattice.bounded_lattice α] (x y : α) : is_minimal x → (x ⊓ y = ⊥ ∨ x ⊓ y = x) :=
begin
  intros,
  cases lt_or_eq_of_le (@lattice.inf_le_left _ _ x y),
  exact or.inl (a.elim_right _ h),
  finish
end

def is_simple (N : Module R) := is_minimal (⊤ : submodule R N)

lemma submodule_of_bot_is_bot : ∀ (A : submodule R (⊥ : submodule R M)), A = ⊥ :=
begin
  intros,
  apply submodule.ext,
  intros,
  split,
    have q : (x : (⊥ : submodule R M)) = 0 := begin
      have r := subtype.mem x,
      have q := set.mem_singleton_iff.elim_left r,
      apply subtype.ext.elim_right,
      finish
    end,
    finish,
  intro,
  have q := set.eq_of_mem_singleton a,
  rw q,
  finish
end

lemma simple_is_minimal (N : submodule R M) : is_simple R N → is_minimal N :=
begin
  intros,
  dunfold is_minimal,
  split,
    have h : N = ⊥ → (⊤ : submodule R N) = ⊥ := begin
      intro,
      have i := submodule_of_bot_is_bot R (⊤ : submodule R (⊥ : submodule R M)),
      finish
    end,
    intro,
    apply a.elim_left,
    finish,
  intros,
  let f := submodule.map_subtype.order_iso N,
  have t := a.elim_right (f.symm ⟨y, le_of_lt a_1 ⟩),
  have v := @order_iso.ord _ _ _ _ f.symm ⟨y, le_of_lt a_1⟩ ⟨N, le_of_eq rfl ⟩ ,
  have w := order_isom_preserves_lt (⟨y, le_of_lt a_1 ⟩: {p // p≤ N}) (⟨N, le_of_eq rfl⟩ : {p // p≤ N}) f.symm a_1,
  have z : ⊤ = (⟨N , le_of_eq rfl⟩ : {p // p ≤ N}) := rfl,
  have v : (order_iso.symm f) ⟨y, le_of_lt a_1 ⟩ < ⊤ := 
  begin
    rw (order_isom_preserves_top (f.symm)).symm,
    apply order_isom_preserves_lt (⟨y, _⟩ : {p //p ≤ N}) ⊤ (f.symm),
    finish
  end,
  have q : (order_iso.symm f) ⟨y, le_of_lt a_1 ⟩ = ⊥ := a.elim_right _ v,
  have q' : (⟨y, le_of_lt a_1 ⟩ : {p // p ≤ N}) = ⊥ := begin
    rw (order_iso.apply_symm_apply f (⊥ : {p // p ≤ N})).symm,
    rw order_isom_preserves_bot f.symm,
    rw (order_iso.apply_symm_apply f (⟨y, _⟩  : {p // p ≤ N})).symm,
    rw q
  end,
  exact subtype.ext.elim_left q'
end

variables (S₁ S₂ : submodule R M)

lemma intersection_with_simple_is_whole_or_trivial :
 is_simple R S₁ → 
 S₁ ⊓ S₂ = ⊥ ∨ (S₁ ⊓ S₂ : submodule R M) = S₁ :=
begin
  intros,
  apply inf_with_minimal_bot_or_idem,
  exact @simple_is_minimal R _ M S₁ a
end

lemma intersection_with_simple_is_simple_or_trivial :
 is_simple R S₁ → 
 S₁ ⊓ S₂ = ⊥ ∨ is_simple R (S₁ ⊓ S₂ : submodule R M) :=
begin
  intros,
  cases intersection_with_simple_is_whole_or_trivial _ _ _ a,
    finish,
  apply or.inr,
  rw h,
  finish
end