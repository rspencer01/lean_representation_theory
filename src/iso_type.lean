import .Module
import .lattices
import logic.function
import .module_trivialities

variables {R : Type} [ring R]


@[simp]
def is_simple (M : Module R) := (¬ is_trivial M) ∧ (∀ (N : submodule R M), N = ⊤ ∨ N = ⊥)

lemma bot_is_trivial (M : Module R) : is_trivial ((⊥ : submodule R M) : Module R) := ⟨{
  hom := 0,
  inv := 0,
  hom_inv_id' := 
  begin
    apply Module.hom_ext',
    intros,
    rw Module.module_hom_comp,
    apply function.funext_iff.2,
    intros,
    simp[*],
    exact eq.symm (submodule.eq_zero_of_bot_submodule a)
   end,
  inv_hom_id' :=
  begin
    apply Module.hom_ext',
    intros,
    rw Module.module_hom_comp,
    simp,
    apply function.funext_iff.2,
    intros,
    simp[*],
    exact eq.symm (eq_zero_of_zero_module a)
   end,

}⟩ 

lemma intersection_of_simples_is_left_or_trivial (M : Module R) (S₁ S₂ : submodule R M) :
 (is_simple (S₁ : Module R)) → (is_simple (S₂ : Module R)) → 
 (is_trivial ((S₁ ⊓ S₂ : submodule R M) : Module R)) ∨ ((S₁ ⊓ S₂ : submodule R M) : Module R) = S₁ :=
begin
  intros,
  set S₃ : submodule R M := S₁ ⊓ S₂,
  set f := (submodule.map_subtype.order_iso S₁).symm,
  set f' := (submodule.map_subtype.order_iso S₁),
  have h : S₃ ≤ S₁ := by simp,
  set S₃' := f ⟨ S₃ , h ⟩ ,
  cases a.elim_right S₃',
    have k : (⟨ S₃ , h ⟩ : {a // a ≤ S₁ }) = (⊤ : {a // a ≤ S₁}) := (
    calc (⟨ S₃ , h ⟩ : {a // a ≤ S₁ }) = f' (f ⟨S₃, h⟩ ) : by rw order_iso.apply_symm_apply 
                                   ... = f' S₃' : rfl
                                   ... = f' ⊤ : (by rw h_1; refl)
                                   ... = ⊤ : order_isom_preserves_top f'),
    have l : S₃ = S₁ := calc 
      S₃ = (⟨ S₃, h⟩ : {a // a ≤ S₁}).val : by simp 
      ... = (⊤ : {a // a ≤ S₁}).val : by rw k
      ... = S₁ : by refl,
    rw l,
    apply or.inr,
    refl,
  have i : (⟨ S₃ , h ⟩ : {a // a ≤ S₁ }) = (⊥ : {a // a ≤ S₁}) := (
    calc (⟨ S₃ , h ⟩ : {a // a ≤ S₁ }) = f' (f ⟨S₃, h⟩ ) : by rw order_iso.apply_symm_apply 
                                   ... = f' S₃' : rfl
                                   ... = f' ⊥ : (by rw h_1; refl)
                                   ... = ⊥ : order_isom_preserves_bot f'),
    have j : S₃ = ⊥ := calc 
       S₃ = (⟨ S₃, h⟩ : {a // a ≤ S₁}).val : by simp 
      ... = (⊥ : {a // a ≤ S₁}).val : by rw i
      ... = ⊥ : by refl,
    rw j,
    exact or.inl (bot_is_trivial _),
end