import order.bounded_lattice

variables {α β : Type} [lattice.bounded_lattice α] [lattice.bounded_lattice β]

def preserves_meet (f : α → β) := ∀ a₁ a₂, f(a₁ ⊓ a₂) = f(a₁) ⊓ f(a₂)
def preserves_join (f : α → β) := ∀ a₁ a₂, f(a₁ ⊔ a₂) = f(a₁) ⊔ f(a₂)
def preserves_top (f : α → β) := f ⊤ = ⊤ 
def preserves_bot (f : α → β) := f ⊥ = ⊥

variables (f : α → β) 

-- Any homomorphism that preserves the meet on a lattice preserves the ≤
theorem homo_preserves_lt_1 (h₁ : preserves_meet f) : 
  ∀ a₁ a₂, a₁ ≤ a₂ → f(a₁) ≤ f(a₂) :=
begin
  intros;
  have h₃ : a₁ = a₁ ⊓ a₂ := eq.symm (lattice.inf_of_le_left a);
  rw [h₃, h₁];
  exact lattice.inf_le_right
end

-- Any injective homorphism that preserves the meet on a lattice resepects ≤ in the preimage
theorem homo_preserves_lt_2 (h₀ : function.injective f) (h₁ : preserves_meet f) : 
  ∀ a₁ a₂, f(a₁) ≤ f(a₂) → a₁ ≤ a₂ :=
begin
  intros;
  have h₃ : f(a₁) = f(a₁) ⊓ f(a₂) := eq.symm (lattice.inf_of_le_left a);
  have h₄ : f(a₁) = f(a₁ ⊓ a₂) := (by rw h₁ a₁ a₂; apply h₃);
  have h₅ : a₁ = a₁ ⊓ a₂ := h₀ h₄;
  exact lattice.le_of_inf_eq (eq.symm h₅)
end

-- A bounded lattice homomorphism is a morphism preserving meet, join, top and bottom
class is_lattice_hom :=
  (preserves_meet : preserves_meet f)
  (preserves_join : preserves_join f)
  (preserves_top : preserves_top f)
  (preserves_bottom : preserves_bot f)