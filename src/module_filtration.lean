import linear_algebra.basic
import data.list.basic

import .lattice_filtration
import .Module

import tactic.library_search

variables (R : Type) [ring R] (M : Module R)

variable (F : filtration (submodule R M))

variables (N : Type) [add_comm_group N] [module R N] (U : submodule R N)
def quotient'' {R : Type} [ring R] {N : Type} [add_comm_group N] [module R N] (U : submodule R N) 
  := @Module.of' R _ U.quotient (submodule.quotient.add_comm_group _) (submodule.quotient.module _)

/- This is insanely ugly.  Why on earth can lean not find the
   instance of `add_comm_group` for an element of type `submodule R M`???  Its causing so many headaches! -/
def subquotient : filtration.le_pair (submodule R M) → Type := 
  λ p, @submodule.quotient R p.b _ (submodule.add_comm_group _) _ (@submodule.comap _ _ _ _ (submodule.add_comm_group _) _ _ _ p.b.subtype p.a) 

def subquotient' (p : filtration.le_pair (submodule R M)) := 
  @quotient'' R _ (p.b) (submodule.add_comm_group p.b) _ (@submodule.comap R p.b M _ (submodule.add_comm_group p.b) _ _ _ (@submodule.subtype R M _ _ _ p.b ) p.a)
  
def is_trivial {R} [ring R] (M : Module R):= ∃ (f : M ≅ 0), true
def is_simple {R} [ring R] (M : Module R) := (¬ is_trivial M) ∧ (∀ (N : submodule R M), N < (⊤ : submodule R M) → N = (⊥ : submodule R M))

def filtration.is_composition_series : Prop :=  ∀ p ∈ F.factors, is_simple (subquotient' R M p)
