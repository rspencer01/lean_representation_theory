import algebra.category.Module.basic
import logic.unique
import data.set.basic

variables {R : Type} [ring R] (M : Module R)

def is_trivial (R : Type) [ring R] (M : Module R) := nonempty (M ≅ 0)

@[simp]
lemma eq_zero_of_zero_module (a : (0 : Module R)) : a = 0
  := punit.unique.uniq a

lemma eq_zero_of_elts_of_trivial_module (f : M ≅ 0) (a : M) : a = 0 :=
  calc a = ((𝟙 M) : M → M) a : by simp
     ... = (f.hom ≫ f.inv) a : by rw f.hom_inv_id
     ... = f.inv (f.hom a) : rfl
     ... = f.inv 0 : by rw (eq_zero_of_zero_module (f.hom a))
     ... = 0 : by simp

lemma bot_isom_trivial (M : Module R) : ((⊥ : submodule R M) : Module R) ≅ 0 := {
  hom := 0,
  inv := 0,
  hom_inv_id' := 
  begin
    apply Module.hom_ext',
    rw Module.module_hom_comp,
    apply function.funext_iff.2,
    intros,
    simp[*],
    exact eq.symm (submodule.eq_zero_of_bot_submodule a)
   end,
  inv_hom_id' :=
  begin
    apply Module.hom_ext',
    rw Module.module_hom_comp,
    simp,
    apply function.funext_iff.2,
    intros,
    simp[*],
    exact eq.symm (eq_zero_of_zero_module a)
   end,
}

lemma bot_is_trivial (M : Module R) : is_trivial R (⊥ : submodule R M) := ⟨ bot_isom_trivial M ⟩

lemma isom_trivial_is_bot (M : Module R) (N : submodule R M) : is_trivial R N → N = ⊥ :=
begin
  intros,
  apply nonempty.elim a,
  intro f,
  have h : ∀ x: N, x = 0 := eq_zero_of_elts_of_trivial_module _ f,
  apply submodule.ext,
  intro,
  split,
    swap,
    intro,
    have i : x = 0 := set.eq_of_mem_singleton a_1,
    finish,
  intro,
  have q := h ⟨ x, a_1 ⟩ ,
  apply set.mem_singleton_of_eq,
  exact subtype.ext.elim_left q
end