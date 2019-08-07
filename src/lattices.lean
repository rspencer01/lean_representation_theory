import order.bounded_lattice
import order.order_iso
import order.complete_lattice

variables {α β : Type} [lattice.bounded_lattice α] [lattice.bounded_lattice β]

@[simp]
def preserves_meet (f : α → β) := ∀ a₁ a₂, f(a₁ ⊓ a₂) = f(a₁) ⊓ f(a₂)
@[simp]
def preserves_join (f : α → β) := ∀ a₁ a₂, f(a₁ ⊔ a₂) = f(a₁) ⊔ f(a₂)
@[simp]
def preserves_top (f : α → β) := f ⊤ = ⊤ 
@[simp]
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
  (preserves_bot : preserves_bot f)


variables {γ δ : Type} [lattice.bounded_lattice γ] [lattice.bounded_lattice δ] (g : ((≤) : γ → γ → Prop)  ≃o ((≤) : δ → δ → Prop))

theorem order_isom_preserves_bot : preserves_bot g :=
begin
  intros,
  dunfold preserves_bot,
  rw lattice.eq_bot_iff,
  let p := (order_iso.to_equiv g).inv_fun ⊥,
  have h : ⊥ ≤ p := lattice.bot_le,
  have i : g ⊥ ≤ g p := (iff.elim_left (order_iso.ord g)) h,
  have j : g p = ⊥ := calc
   g p = g.to_equiv.to_fun ((g.to_equiv).inv_fun ⊥) : by simp
   ... = ⊥ : by rw (order_iso.to_equiv g).right_inv ⊥
   ,
  rw eq.symm j,
  assumption
end

theorem order_isom_preserves_top : preserves_top g :=
begin
  intros,
  dunfold preserves_top,
  rw lattice.eq_top_iff,
  let p := (order_iso.to_equiv g).inv_fun ⊤,
  have h : ⊤ ≥ p := lattice.le_top,
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
  have h₁ : g (a₁ ⊓ a₂) ≤ g a₁ := iff.elim_left (order_iso.ord g) lattice.inf_le_left,
  have h₂ : g (a₁ ⊓ a₂) ≤ g a₂ := iff.elim_left (order_iso.ord g) lattice.inf_le_right,
  exact (iff.elim_right lattice.le_inf_iff) ⟨ h₁ , h₂ ⟩,
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
  have h₁ : g (a₁ ⊔ a₂) ≥ g a₁ := iff.elim_left (order_iso.ord g) lattice.le_sup_left,
  have h₂ : g (a₁ ⊔ a₂) ≥ g a₂ := iff.elim_left (order_iso.ord g) lattice.le_sup_right,
  exact (iff.elim_right lattice.sup_le_iff) ⟨ h₁ , h₂ ⟩,
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

instance order_is_is_lattice_hom : is_lattice_hom g := {
  preserves_meet := @order_isom_preserves_meet _ _ _ _ g,
  preserves_join := @order_isom_preserves_join _ _ _ _ g,
  preserves_top := @order_isom_preserves_top _ _ _ _ g,
  preserves_bot := @order_isom_preserves_bot _ _ _ _ g
}

variable (A : α)


/- TODO This is stronger than needed.  We can just let α be an order_bot and a lattice. -/
instance : lattice.bounded_lattice (subtype (λ a, a ≤ A)) := {
  inf := λ x y, ⟨(x : α) ⊓ (y : α), le_trans lattice.inf_le_left x.property ⟩,
  sup := λ x y, ⟨(x : α) ⊔ (y : α), lattice.sup_le_iff.elim_right ⟨ x.property, y.property ⟩ ⟩,
  le_sup_left := λ a b, @lattice.le_sup_left α _ a b,
  le_sup_right := λ a b, @lattice.le_sup_right α _ a b,
  sup_le := λ a b c h₁ h₂, (@lattice.sup_le_iff α _ _ _ _).elim_right ⟨ h₁ , h₂ ⟩,
  inf_le_left := λ a b, @lattice.inf_le_left α _ a b,
  inf_le_right := λ a b, @lattice.inf_le_right α _ a b,
  le_inf := λ a b c h₁ h₂, (@lattice.le_inf_iff α _ _ _ _).elim_right ⟨ h₁ , h₂ ⟩  ,
  top := ⟨ A , le_refl A ⟩ ,
  le_top := λ a, a.property ,
  bot := ⟨ ⊥ , lattice.bounded_lattice.bot_le A ⟩,
  bot_le := λ a, @lattice.bot_le α _ a ,
  ..subtype.partial_order _
}
