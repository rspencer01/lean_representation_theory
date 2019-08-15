import algebra.module
import algebra.punit_instances
import category_theory.types
import linear_algebra.basic

universe u

open category_theory

variables (R : Type u) [ring R]

/-- An example of a module for any ring is the zero module -/
instance zero_module : module R punit := module.of_core $ 
  by refine {
    smul := λ _ _, punit.star,
    .. punit.comm_ring, ..}; 
    intros; exact subsingleton.elim _ _

/-- The category of R-modules and their morphisms. -/
structure Module :=
  (carrier : Type)
  (prop_add_comm_group : add_comm_group carrier)
  (prop_module : module R carrier)

lemma id_is_linear (M : Type) [add_comm_group M] [module R M] : is_linear_map R (@id M) := {
  add := λ x y,  (by repeat {apply id.def}),
  smul := λ c x, (by repeat {apply id.def}),
}

lemma linear_maps_comp (A B C : Type) [add_comm_group A] [module R A] [add_comm_group B] [module R B] [add_comm_group C] [module R C]
   (f : A → B) (g : B → C) (h₁ : is_linear_map R f) (h₂ : is_linear_map R g)
  : is_linear_map R (g ∘ f) := {
  add := λ x y,  (by simp; rw is_linear_map.add R f; rw is_linear_map.add R g),
  smul := λ c x, (by simp; rw is_linear_map.smul f c; rw is_linear_map.smul g c)
}

namespace Module 
  instance : has_coe_to_sort (Module R) :=
    { S := Type, coe := Module.carrier}
end Module 

instance Module_add_comm_group (M: Module R) : add_comm_group M := M.prop_add_comm_group
instance Module_R_module (M: Module R) : module R M := M.prop_module

namespace Module
  def of (X : Type) [h₁ : add_comm_group X] [h₂ : module R X] : Module R := ⟨ X , h₁ , h₂⟩

  instance : has_zero (Module R) := ⟨ of R punit ⟩

  variables (M N U : Module R)

  instance : category (Module R) := {
    hom := λ M N, M →ₗ[R] N,
    id := λ M, 1 ,
    comp := λ A B C f g, g.comp f ,
  }
 
  @[simp] lemma module_id : linear_map.to_fun (𝟙 M) = id := rfl

  @[simp] lemma module_hom_comp (f : M ⟶ N) (g : N ⟶ U) :
    ((f ≫ g) : M → U) = g.to_fun ∘ f.to_fun := rfl

  instance : has_coe_to_fun (M ⟶ N) :=
    { F   := λ f, M → N,
      coe := λ f, (f : M → N) }

  @[extensionality] lemma hom_ext  {f g : M ⟶ N} : (∀ x : M, f x = g x) → f = g :=
    λ w, linear_map.ext w

  @[extensionality] lemma hom_ext'  {f g : M ⟶ N} : (f : M → N) = g → f = g :=
    λ w, hom_ext R M N (function.funext_iff.1 w)

  @[simp] lemma coe_id {M : Module R} : ((𝟙 M) : M → M) = id := rfl

  instance hom_is_module_hom {M₁ M₂ : Module R} (f : M₁ ⟶ M₂) :
    is_linear_map R (f : M₁ → M₂) := linear_map.is_linear _

end Module

instance (M : Type) [add_comm_group M] [module R M] : has_coe (submodule R M) (Module R) := ⟨ λ N, Module.of R N ⟩

def are_isomorphic {R} [ring R] (M₁ M₂ : Module R) := nonempty (M₁ ≅ M₂)
