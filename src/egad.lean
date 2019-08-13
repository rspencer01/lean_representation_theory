import data.multiset
import data.finset
import data.list.basic
import .module_filtration
import .quiver
import .lattices

variables {R : Type} [ring R] {M : Module R}

variable (F : filtration (submodule R M))

structure generalised_alperin_diagram :=
  (diagram : quiver)
  (ac : is_acyclic diagram)
  (s : diagram.vertices → { a // a ∈ F.factors })
  (bs : function.bijective s)
  (delta : downset diagram.vertices → submodule R M)
  (id : function.injective delta)
  (lat_hom : is_lattice_hom delta)

instance : has_coe (generalised_alperin_diagram F) quiver := ⟨ λ D, generalised_alperin_diagram.diagram D⟩

variable (D : generalised_alperin_diagram F)

instance gad_is_acyclic (D : generalised_alperin_diagram F) : is_acyclic D := D.ac
instance gad_is_pordered : partial_order (D : quiver).vertices := quiver_vertices_partial _

theorem t_1_2 : 
    ∀ (A B : downset (D : quiver).vertices), A ≤ B ↔ D.delta A ≤ D.delta B :=
    begin
      intros;
      split;
        intros;
        have h₁ : preserves_meet D.delta := D.lat_hom.preserves_meet,
        exact homo_preserves_lt_1 D.delta h₁ A B a,
        have h₂ : function.injective D.delta := D.id;
        exact homo_preserves_lt_2 _ h₂ h₁ _ _ a
    end
