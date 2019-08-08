import data.list

universes U₁ U₂

def nonempty_list (γ : Type U₁) := {l : list γ // l ≠ []}

namespace nonempty_list
  variable {γ : Type U₁}
  
  @[simp]
  def last (l : nonempty_list γ) := list.last l.val l.property


  @[simp]
  def head : nonempty_list γ → γ 
  | ⟨[]      , h ⟩ := absurd rfl h
  | ⟨ x :: t , _ ⟩ := x

end nonempty_list

namespace list
  variables {α : Type U₁} {β : Type U₂}

  -- Much like head, but doesn't require α to be inhabited
  @[simp] def head'': Π  (L : list α), L ≠ [] → α
  | []        h := absurd rfl h
  | (x :: xs) h := x

  variables {R : α → α → Prop} {x y : α} {L L₁ L₂ : list α}

  @[simp]
  lemma chain'_desc_left : chain' R (x :: L) → chain' R L := by cases L; simp[chain']

  def chain'_apply_between (f : Π(a b : α), (R a b) → β) : Π (L : list α), list.chain' R L → list β 
  | [] h := []
  | [x] h := []
  | (x :: y :: xs) h := (f x y (rel_of_chain_cons h)) :: 
                       (chain'_apply_between (y :: xs) (chain'_desc_left h) )

  @[simp]
  lemma chain'_of_two : chain' R [x, y] ↔ R x y := by dunfold chain'; exact chain_singleton

  lemma chain'_of_first_two : chain' R (x :: y :: L) → R x y := by dunfold chain'; simp; exact λ a b, a

  lemma chain'_append : Π (L₁ : list α) (h : L₁ ≠ []) (x : α), (R (L₁.last h) x) → (chain' R L₁) → chain' R (L₁ ++ [x])
  | [] h           _ _  _  := absurd rfl h
  | [a] h         x h₁ h₂ := (by simp; assumption) 
  | (a :: b :: l) h  x h₁ h₂ := iff.elim_right (@chain'_split α R b [a] (l ++ [x])) 
      ⟨ iff.elim_right chain'_of_two (chain'_of_first_two h₂), 
        chain'_append  (b :: l) _ x h₁ (chain'_desc_left h₂) ⟩ 
  

  lemma chain'_concat' : Π (L₁ L₂ : nonempty_list α), (R L₁.last L₂.head) → (chain' R L₁.val) → (chain' R L₂.val) → chain' R (L₁.val ++ L₂.val)
  | ⟨ [] , h₁ ⟩ _ _ _ _ := absurd rfl h₁ 
  | _ ⟨ [] , h₁ ⟩ _ _ _ := absurd rfl h₁ 
  | ⟨ x₁ :: l₁ , h₁ ⟩ ⟨ x₂ :: l₂ , h₂ ⟩ h₃ s₁ s₂ := 
    begin
      intros;
      apply iff.elim_right chain'_split;
      simp;
      apply and.intro,
      have k : nonempty_list.head ⟨x₂ :: l₂, h₂⟩ = x₂ := rfl,
      cases l₁,
      simp,
      have j : nonempty_list.last ⟨[x₁], h₁⟩ = x₁ := rfl,
      have l : chain' R [x₁ , x₂] := iff.elim_right (@chain'_of_two α R x₁ x₂) h₃,
      exact (iff.elim_left chain'_of_two) l,
      simp,
      apply @chain'_append α R (x₁ :: l₁_hd :: l₁_tl),
      apply h₃,
      assumption,
      assumption
    end

  def apply_between (f : α → α → β) : list α → list β
  | [] := []
  | [x] := []
  | (x :: y :: xs) := (f x y) :: apply_between (y :: xs)


end list