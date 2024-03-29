import linear_algebra.basic
import data.list.basic

import .lattice_filtration
import .Module
import .module_trivialities

import tactic.library_search

namespace submodule
  variables {R : Type} [ring R] {N : Type} [add_comm_group N] [module R N]
  /- Given a submodule `U` of a module `N`, returns the quotient `N/U` as a Module -/
  def quotient' (U : submodule R N) := Module.of R U.quotient
end submodule

variables {R : Type} [ring R] {M : Module R}

variable (F : filtration (submodule R M))

def subquotient (p : filtration.le_pair (submodule R M)) := 
  (submodule.comap p.val.2.subtype p.val.1).quotient'
  
def is_simple (M : Module R) := (¬ is_trivial M) ∧ (∀ (N : submodule R M), N = ⊤ ∨ N = ⊥)

def filtration.is_s_filtration (S : set (Module R)) (F : filtration (submodule R M)) : Prop
  := ∀ p ∈ F.factors, (subquotient p) ∈ S

def filtration.is_composition_series (F : filtration (submodule R M)) : Prop
  := filtration.is_s_filtration is_simple F

def filtration.factor_modules (F : filtration (submodule R M)) : list (Module R)
  := F.factors.map subquotient 