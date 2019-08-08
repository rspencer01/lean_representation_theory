import order.lattice
import order.bounded_lattice
import group_theory.category
import linear_algebra.basic

import .quiver
import .modules
import .lists
import .lattices
import .subsets

open classical

universe u

variables {R : Type} [ring R] {M : modules R} [decidable_eq M.space] [decidable_eq (modules R)]

variables (U V : submodules M)

class filtration (M : modules R) := 
  (mods : list (submodules M))
  (is_fil : list.chain' (has_le.le) mods)

def quotient' (U : submodules M) : modules R := {
  space := submodule.quotient U,
  acg := by apply_instance,
  mod := by apply_instance
}

def mk_quotient (U V : submodule R (M : Type)) (l : U ≤ V) : Type :=
  submodule.quotient ((submodule.map_subtype.order_iso V).inv_fun ⟨U, l⟩)

def mk_quotient' (U V : submodule R (M : Type)) : U ≤ V → modules R := λ l, {
  space := mk_quotient U V l,
  acg := by dunfold mk_quotient; apply_instance,
  mod := by dunfold mk_quotient; apply_instance
}

def factors (F : filtration M) : list (modules R) := 
  list.chain'_apply_between mk_quotient' F.mods F.is_fil

def extend (N : submodules M) : 
  filtration (N : modules R) → filtration (quotient' N) → filtration M := λ F₁ F₂ , {
    mods := (list.map (submodules.lift' R M N) F₁.mods) ++ 
            [N] ++ 
            (list.map (submodule.comap_mkq.order_iso N).to_fun F₂.mods),
    is_fil := sorry
  }

variable (F : filtration M)

structure generalised_alperin_diagram :=
  (diagram : quiver)
  [ac : is_acyclic diagram]
  (s : diagram.vertices → (factors F).to_finset.to_set)
  [bs : function.bijective s]
  (delta : downset diagram.vertices → submodules M)
  [id : function.injective delta]
  [lat_hom : is_lattice_hom delta]

variable (D : generalised_alperin_diagram F)

theorem t_1_2 (F : filtration M) (D : generalised_alperin_diagram F) : 
    ∀ (A B : @downset D.diagram.vertices (@quiver_vertices_partial D.diagram D.ac)), A ≤ B ↔ D.delta A ≤ D.delta B :=
    begin
      intros;
      split;
        intros;
        exact @homo_preserves_lt_1 (@downset D.diagram.vertices (@quiver_vertices_partial D.diagram D.ac)) (submodules M) (s_bounded_lattice _ _ _ _ _) _ D.delta _ A B a
    end