import algebra.module
import group_theory.category
import algebra.ring

import category_theory.concrete_category

universe u

open category_theory

variables (R : Type u) [ring R]

/-- A bundled statement that the type `M` is both an additive
    commutative group and an R-module -/
class r_mod (M : Type u) extends add_comm_group M , module R M

/-- An example of a module for any ring is the zero module -/
instance zero_module : module R punit := module.of_core $ 
  by refine {
    smul := λ _ _, punit.star,
    .. punit.comm_ring, ..}; 
    intros; exact subsingleton.elim _ _

instance zero_r_mod : r_mod R punit := {..zero_module R}

instance add_comm_group_and_module_to_r_mod (M : Type u) [h₁ : add_comm_group M] [h₂ : module R M] : r_mod R M := {..h₁,..h₂}

def is_R_linear_map (M N : Type u) [r_mod R M] [r_mod R N] : (M → N) → Prop := is_linear_map R

/- This is defined in the bundled `linear_map` but here it is defined again
   because I don't know how to massage it correctly, and doing that would
   be slower than writing this out. -/
lemma is_R_linear_map_comp (M N U : Type u) [r_mod R M] [r_mod R N] [r_mod R U] 
  (g : N → U) (f : M → N) [h₁ : is_R_linear_map R _ _ g] [h₂ : is_R_linear_map R _ _ f] : is_R_linear_map R _ _ (g ∘ f) :=
  {
      add := λ x y,  calc
        (g ∘ f) (x + y) = g ( f (x + y))        : by simp
                    ... = g ( (f x)+ (f y))     : by rw @is_linear_map.add R _ _ _ _ _ _ _ f h₂ _ _
                    ... = (g (f x)) + (g (f y)) : by rw @is_linear_map.add R _ _ _ _ _ _ _ g h₁ _ _
      ,
      smul := λ c x, calc
        (g ∘ f) (c • x) = g (f (c • x)) : by simp
                    ... = g (c • (f x)) : by rw @is_linear_map.smul R _ _ _ _ _ _ _ f h₂ _ _
                    ... = c • (g (f x)) : by rw @is_linear_map.smul R _ _ _ _ _ _ _ g h₁ _ _
      ,
  }

/- This is defined in the bundled `linear_map` but here it is defined again
   because I don't know how to massage it correctly, and doing that would
   be slower than writing this out. -/
lemma is_R_linear_map_id (M : Type u) [r_mod R M] : is_R_linear_map R M M id :=
  {
      add := λ x y,  (by repeat {apply id.def}),
      smul := λ c x, (by repeat {apply id.def}),
  }

/-- The category of R-modules and their morphisms. -/
@[reducible] def Module : Type (u+1) := bundled (r_mod R)

namespace Module
  variables (M N : Module R)

  instance : r_mod R M := M.str
  instance : add_comm_group M := by apply_instance
  instance : module R M := by apply_instance

  instance concrete_is_module_hom : 
    concrete_category (is_R_linear_map R) :=
    { hom_id := (λ α ia, @is_R_linear_map_id R _ α ia ) , 
      hom_comp := (λ α β γ ia ib ic g f lg lf, @is_R_linear_map_comp R _ α β γ ia ib ic _ _ lg lf )}

  def of (X : Type u) [r_mod R X] : Module R := ⟨ X ⟩ 
  def of' (X : Type u) [add_comm_group X] [module R X] : Module R := ⟨ X ⟩ 

  instance hom_is_module_hom {M₁ M₂ : Module R} (f : M₁ ⟶ M₂) :
    is_linear_map R (f : M₁ → M₂) := f.2

  instance : has_zero (Module R) := ⟨ @of R _ punit (zero_r_mod R) ⟩

end Module