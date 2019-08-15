import .Module
import .lattices
import logic.function
import .module_trivialities
import ring_theory.algebra

variables {R : Type} [ring R] (M : Module R) (S₁ S₂ : submodule R M)

@[simp]
def is_simple := (¬ is_trivial M) ∧ (∀ (N : submodule R M), N = ⊤ ∨ N = ⊥)

lemma intersection_of_simples_is_left_or_trivial :
 (is_simple (S₁ : Module R)) → (is_simple (S₂ : Module R)) → 
 (is_trivial ((S₁ ⊓ S₂ : submodule R M) : Module R)) ∨ ((S₁ ⊓ S₂ : submodule R M) : Module R) = S₁ :=
begin
  intros,
  set S₃ : submodule R M := S₁ ⊓ S₂,
  set f := (submodule.map_subtype.order_iso S₁).symm,
  set f' := (submodule.map_subtype.order_iso S₁),
  have h : S₃ ≤ S₁ := by simp,
  set S₃' := f ⟨ S₃ , h ⟩ ,
  cases a.elim_right S₃',
    have k : (⟨ S₃ , h ⟩ : {a // a ≤ S₁ }) = (⊤ : {a // a ≤ S₁}) := (
    calc (⟨ S₃ , h ⟩ : {a // a ≤ S₁ }) = f' (f ⟨S₃, h⟩ ) : by rw order_iso.apply_symm_apply 
                                   ... = f' S₃' : rfl
                                   ... = f' ⊤ : (by rw h_1; refl)
                                   ... = ⊤ : order_isom_preserves_top f'),
    have l : S₃ = S₁ := calc 
      S₃ = (⟨ S₃, h⟩ : {a // a ≤ S₁}).val : by simp 
      ... = (⊤ : {a // a ≤ S₁}).val : by rw k
      ... = S₁ : by refl,
    rw l,
    apply or.inr,
    refl,
  have i : (⟨ S₃ , h ⟩ : {a // a ≤ S₁ }) = (⊥ : {a // a ≤ S₁}) := (
    calc (⟨ S₃ , h ⟩ : {a // a ≤ S₁ }) = f' (f ⟨S₃, h⟩ ) : by rw order_iso.apply_symm_apply 
                                   ... = f' S₃' : rfl
                                   ... = f' ⊥ : (by rw h_1; refl)
                                   ... = ⊥ : order_isom_preserves_bot f'),
    have j : S₃ = ⊥ := calc 
       S₃ = (⟨ S₃, h⟩ : {a // a ≤ S₁}).val : by simp 
      ... = (⊥ : {a // a ≤ S₁}).val : by rw i
      ... = ⊥ : by refl,
    rw j,
    exact or.inl ⟨ bot_is_trivial _ ⟩ ,
end

lemma intersection_of_simples_is_right_or_trivial (M : Module R) (S₁ S₂ : submodule R M) :
 (is_simple (S₁ : Module R)) → (is_simple (S₂ : Module R)) → 
 (is_trivial ((S₁ ⊓ S₂ : submodule R M) : Module R)) ∨ ((S₁ ⊓ S₂ : submodule R M) : Module R) = S₂ := 
begin
  intros,
  rw lattice.inf_comm,
  exact intersection_of_simples_is_left_or_trivial M S₂ S₁ a_1 a
end

lemma intersection_of_simples_is_simple_or_trivial (M : Module R) (S₁ S₂ : submodule R M) :
 (is_simple (S₁ : Module R)) → (is_simple (S₂ : Module R)) → 
 (is_trivial ((S₁ ⊓ S₂ : submodule R M) : Module R)) ∨ is_simple ((S₁ ⊓ S₂ : submodule R M) : Module R) := 
begin
  intros,
  cases intersection_of_simples_is_left_or_trivial M S₁ S₂ a a_1,
  exact or.inl h,
  rw h,
  exact or.inr a
end

theorem isom_is_equiv : equivalence (@are_isomorphic R _) := 
  ⟨ λ x, ⟨ category_theory.iso.refl x ⟩,
    λ x y h, h.elim (λ f, ⟨ category_theory.iso.symm f ⟩), 
    λ x y z h₁ h₂, h₁.elim (λ f, h₂.elim (λ g, ⟨category_theory.iso.trans f g⟩)) ⟩

def isomorphism_class_of_modules := quotient ⟨(@are_isomorphic R _), isom_is_equiv ⟩