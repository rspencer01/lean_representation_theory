import data.set
import order
import order.zorn

open classical

variables {α : Type} [lattice.complete_lattice α] (S : set α)

variables (inf' : ∀ a b : S, (a : α) ⊓ (b : α) ∈ S)
variables (sup' : ∀ a b : S, (a : α) ⊔ (b : α) ∈ S)
variables (bot' : (⊥ : α) ∈ S)
variables (top' : (⊤ : α) ∈ S)

instance s_has_le : has_le S := ⟨ λ a b, (a : α) ≤ b ⟩
instance s_has_lt : has_le S := ⟨ λ a b, (a : α) < b ⟩
instance s_has_inf : lattice.has_inf S := ⟨ λ a b, ⟨ (a : α) ⊓ (b : α), inf' _ _ ⟩ ⟩ 
instance s_has_sup : lattice.has_sup S := ⟨ λ a b, ⟨ (a : α) ⊔ (b : α), sup' _ _ ⟩ ⟩ 
instance s_has_bot : lattice.has_bot S := ⟨ ⟨ (⊥ : α) , bot' ⟩ ⟩
instance s_has_top : lattice.has_top S := ⟨ ⟨ (⊤ : α) , top' ⟩ ⟩

instance s_complete_lattice : lattice.bounded_lattice S := {
    le_refl := assume a, by simp,
    le_antisymm := assume a b h1 h2, set_coe.ext (@lattice.complete_lattice.le_antisymm α _ a b h1 h2),
    le_trans := assume a b c h1 h2, @lattice.complete_lattice.le_trans α _ a b c h1 h2,

    sup_le := assume a b c h1 h2, @lattice.complete_lattice.sup_le α _ a b c h1 h2,
    le_sup_left := assume a b, @lattice.complete_lattice.le_sup_left α _ a b,
    le_sup_right := assume a b, @lattice.complete_lattice.le_sup_right α _ a b,
    le_inf := assume a b c h1 h2, @lattice.complete_lattice.le_inf α _ a b c h1 h2,
    inf_le_left := assume a b, @lattice.complete_lattice.inf_le_left α _ a b,
    inf_le_right := assume a b, @lattice.complete_lattice.inf_le_right α _ a b,

    le_top := assume a , @lattice.complete_lattice.le_top α _ a ,
    bot_le := assume a , @lattice.complete_lattice.bot_le α _ a ,

    ..s_has_le S,
    ..s_has_lt S,
    ..s_has_sup S sup',
    ..s_has_inf S inf',
    ..s_has_bot S bot',
    ..s_has_top S top'
}