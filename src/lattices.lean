import order.bounded_lattice
import order.order_iso
import order.complete_lattice

open lattice

variables {α β : Type} [bounded_lattice α] [bounded_lattice β]

@[simp]
def preserves_meet (f : α → β) := ∀ a₁ a₂, f(a₁ ⊓ a₂) = f(a₁) ⊓ f(a₂)
@[simp]
def preserves_join (f : α → β) := ∀ a₁ a₂, f(a₁ ⊔ a₂) = f(a₁) ⊔ f(a₂)

variables (f : α → β) 

-- Any homomorphism that preserves the meet on a lattice preserves the ≤
theorem homo_preserves_lt_1 (h₁ : preserves_meet f) : 
  ∀ a₁ a₂, a₁ ≤ a₂ → f(a₁) ≤ f(a₂) :=
begin
  intros;
  have h₃ : a₁ = a₁ ⊓ a₂ := eq.symm (inf_of_le_left a);
  rw [h₃, h₁];
  exact inf_le_right
end

-- Any injective homorphism that preserves the meet on a lattice resepects ≤ in the preimage
theorem homo_preserves_lt_2 (h₀ : function.injective f) (h₁ : preserves_meet f) : 
  ∀ a₁ a₂, f(a₁) ≤ f(a₂) → a₁ ≤ a₂ :=
begin
  intros;
  have h₃ : f(a₁) = f(a₁) ⊓ f(a₂) := eq.symm (inf_of_le_left a);
  have h₄ : f(a₁) = f(a₁ ⊓ a₂) := (by rw h₁ a₁ a₂; apply h₃);
  have h₅ : a₁ = a₁ ⊓ a₂ := h₀ h₄;
  exact le_of_inf_eq (eq.symm h₅)
end

-- A bounded lattice homomorphism is a morphism preserving meet, join, top and bottom
class is_lattice_hom :=
  (preserves_meet : preserves_meet f)
  (preserves_join : preserves_join f)
  (preserves_top : f ⊤ = ⊤)
  (preserves_bot : f ⊥ = ⊥)


variables {γ δ : Type} [bounded_lattice γ] [bounded_lattice δ] (g : ((≤) : γ → γ → Prop)  ≃o ((≤) : δ → δ → Prop))

theorem order_isom_preserves_bot : g ⊥ = ⊥ :=
begin
  intros,
  rw eq_bot_iff,
  let p := (order_iso.to_equiv g).inv_fun ⊥,
  have h : ⊥ ≤ p := bot_le,
  have i : g ⊥ ≤ g p := (iff.elim_left (order_iso.ord g)) h,
  have j : g p = ⊥ := calc
   g p = g.to_equiv.to_fun ((g.to_equiv).inv_fun ⊥) : by simp
   ... = ⊥ : by rw (order_iso.to_equiv g).right_inv ⊥
   ,
  rw eq.symm j,
  assumption
end

theorem order_isom_preserves_top : g ⊤ = ⊤  :=
begin
  intros,
  rw eq_top_iff,
  let p := (order_iso.to_equiv g).inv_fun ⊤,
  have h : ⊤ ≥ p := le_top,
  have i : g ⊤ ≥ g p := (iff.elim_left (order_iso.ord g)) h,
  have j : g p = ⊤ := calc
   g p = g.to_equiv.to_fun ((g.to_equiv).inv_fun ⊤) : by simp
   ... = ⊤ : by rw (order_iso.to_equiv g).right_inv ⊤
   ,
  rw eq.symm j,
  assumption
end

lemma lem_1 (a₁ a₂ : γ) (g : ((≤) : γ → γ → Prop)  ≃o ((≤) : δ → δ → Prop)) : g (a₁ ⊓ a₂) ≤ g a₁ ⊓ g a₂ :=
begin
  have h₁ : g (a₁ ⊓ a₂) ≤ g a₁ := iff.elim_left (order_iso.ord g) inf_le_left,
  have h₂ : g (a₁ ⊓ a₂) ≤ g a₂ := iff.elim_left (order_iso.ord g) inf_le_right,
  exact (iff.elim_right le_inf_iff) ⟨ h₁ , h₂ ⟩,
end

theorem order_isom_preserves_meet : preserves_meet g := 
begin
  dunfold preserves_meet,
  intros,
  let g' := g.symm,
  have i₁ : g (a₁ ⊓ a₂) ≤ g a₁ ⊓ g a₂ := lem_1 _ _ _,
  have i₂ : g' (g a₁ ⊓ g a₂) ≤ (g' (g a₁)) ⊓ (g' (g a₂)) := lem_1 _ _ _,
  have j : a₁ ⊓ a₂ = (g.symm (g a₁)) ⊓ (g' (g a₂)) := by repeat { rw g.symm_apply_apply },
  have i₃ : g' (g a₁ ⊓ g a₂) ≤ a₁ ⊓ a₂ := (by rw j; exact i₂),
  have i₄ : g a₁ ⊓ g a₂ ≤ g (a₁ ⊓ a₂) := calc
    g a₁ ⊓ g a₂ = g (g' (g a₁ ⊓ g a₂)) : by rw g.apply_symm_apply
            ... ≤ g (a₁ ⊓ a₂) : (iff.elim_left (@order_iso.ord γ δ _ _ g _ _)) i₃ 
  ,
  exact le_antisymm i₁ i₄ 
end

lemma lem_2 (a₁ a₂ : γ) (g : ((≤) : γ → γ → Prop)  ≃o ((≤) : δ → δ → Prop)) : g (a₁ ⊔ a₂) ≥ g a₁ ⊔ g a₂ :=
begin
  have h₁ : g (a₁ ⊔ a₂) ≥ g a₁ := iff.elim_left (order_iso.ord g) le_sup_left,
  have h₂ : g (a₁ ⊔ a₂) ≥ g a₂ := iff.elim_left (order_iso.ord g) le_sup_right,
  exact (iff.elim_right sup_le_iff) ⟨ h₁ , h₂ ⟩,
end

theorem order_isom_preserves_join : preserves_join g := 
begin
  dunfold preserves_join,
  intros,
  let g' := g.symm,
  have i₁ : g (a₁ ⊔ a₂) ≥ g a₁ ⊔ g a₂ := lem_2 _ _ _,
  have i₂ : g' (g a₁ ⊔ g a₂) ≥ (g' (g a₁)) ⊔ (g' (g a₂)) := lem_2 _ _ _,
  have j : a₁ ⊔ a₂ = (g.symm (g a₁)) ⊔ (g' (g a₂)) := by repeat { rw g.symm_apply_apply },
  have i₃ : g' (g a₁ ⊔ g a₂) ≥ a₁ ⊔ a₂ := (by rw j; exact i₂),
  have i₄ : g a₁ ⊔ g a₂ ≥ g (a₁ ⊔ a₂) := calc
    g a₁ ⊔ g a₂ = g (g' (g a₁ ⊔ g a₂)) : by rw g.apply_symm_apply
            ... ≥ g (a₁ ⊔ a₂) : (iff.elim_left (@order_iso.ord γ δ _ _ g _ _)) i₃ 
  ,
  exact le_antisymm i₄ i₁
end

theorem order_isom_preserves_lt (a₁ a₂ : γ) (g : ((≤) : γ → γ → Prop)  ≃o ((≤) : δ → δ → Prop)) : a₁ < a₂ → g a₁ < g a₂ :=
begin
  intros,
  have h : g a₁ ≤ g a₂ := (order_iso.ord g).elim_left (le_of_lt a),
  apply lt_of_le_of_ne,
  assumption,
  simp,
  have i := equiv.injective (g.to_equiv),
  intro,
  have q : a₁ = a₂ := i a_1,
  exact not_lt_of_ge (ge_of_eq q) a
end

instance order_is_is_lattice_hom : is_lattice_hom g := {
  preserves_meet := @order_isom_preserves_meet _ _ _ _ g,
  preserves_join := @order_isom_preserves_join _ _ _ _ g,
  preserves_top := @order_isom_preserves_top _ _ _ _ g,
  preserves_bot := @order_isom_preserves_bot _ _ _ _ g
}

variable (A : α)


/- TODO This is stronger than needed.  We can just let α be an order_bot and a lattice. -/
instance : bounded_lattice (subtype (λ a, a ≤ A)) := {
  inf := λ x y, ⟨(x : α) ⊓ (y : α), le_trans inf_le_left x.property ⟩,
  sup := λ x y, ⟨(x : α) ⊔ (y : α), sup_le_iff.elim_right ⟨ x.property, y.property ⟩ ⟩,
  le_sup_left := λ a b, @le_sup_left α _ a b,
  le_sup_right := λ a b, @le_sup_right α _ a b,
  sup_le := λ a b c h₁ h₂, (@sup_le_iff α _ _ _ _).elim_right ⟨ h₁ , h₂ ⟩,
  inf_le_left := λ a b, @inf_le_left α _ a b,
  inf_le_right := λ a b, @inf_le_right α _ a b,
  le_inf := λ a b c h₁ h₂, (@le_inf_iff α _ _ _ _).elim_right ⟨ h₁ , h₂ ⟩  ,
  top := ⟨ A , le_refl A ⟩ ,
  le_top := λ a, a.property ,
  bot := ⟨ ⊥ , bounded_lattice.bot_le A ⟩,
  bot_le := λ a, @bot_le α _ a ,
  ..subtype.partial_order _
}

/-- A maximal element is a last element before the top -/
def maximal {α : Type} [order_top α] : α → Prop := λ x, x ≠ ⊤ ∧ ∀ y > x, y = ⊤

/-- A minimal element is a first element after the bottom -/
def minimal {α : Type} [order_bot α] : α → Prop := λ x, x ≠ ⊥ ∧ ∀ y < x, y = ⊥

theorem eq_top_of_meet_of_distinct_maximals (a₁ a₂ : α) (h₁ : maximal a₁) (h₂ : maximal a₂) (h_neq : a₁ ≠ a₂) : a₁ ⊔ a₂ = ⊤ :=
begin
  cases lt_or_eq_of_le (@le_sup_right _ _ a₁ a₂) ,
    exact h₂.elim_right _ h,
  have a₁_le : a₁ ≤ a₂ := le_of_sup_eq h.symm,
  cases lt_or_eq_of_le a₁_le,
    have q :=  h₁.elim_right _ h_1,
    have r :=  h₂.elim_left,
    contradiction,
  rw [h_1, sup_idem],
  contradiction
end