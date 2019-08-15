import .Module
import logic.unique

variables {R : Type} [ring R] (M : Module R)

def is_trivial (M : Module R):= are_isomorphic M 0

@[simp]
lemma eq_zero_of_zero_module (a : (0 : Module R)) : a = 0
  := punit.unique.uniq a

lemma eq_zero_of_elts_of_trivial_module (f : M ≅ 0) (a : M) : a = 0 :=
begin
  intros,
  calc a = ((𝟙 M) : M → M) a : by simp
     ... = (f.hom ≫ f.inv) a : by rw f.hom_inv_id
     ... = f.inv (f.hom a) : rfl
     ... = f.inv 0 : by rw (eq_zero_of_zero_module (f.hom a))
     ... = 0 : by simp
end

lemma bot_is_trivial (M : Module R) : ((⊥ : submodule R M) : Module R) ≅ 0 := {
  hom := 0,
  inv := 0,
  hom_inv_id' := 
  begin
    apply Module.hom_ext',
    intros,
    rw Module.module_hom_comp,
    apply function.funext_iff.2,
    intros,
    simp[*],
    exact eq.symm (submodule.eq_zero_of_bot_submodule a)
   end,
  inv_hom_id' :=
  begin
    apply Module.hom_ext',
    intros,
    rw Module.module_hom_comp,
    simp,
    apply function.funext_iff.2,
    intros,
    simp[*],
    exact eq.symm (eq_zero_of_zero_module a)
   end,
}