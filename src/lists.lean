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

  @[simp]
  lemma tail_of_append  (x y : α) (l : list α) : tail (l ++ [y,x]) = tail (l ++ [y]) ++ [x] :=
  by cases l; repeat {simp}

  lemma rev_init_rev_tail : Π (l : list α), l.init.reverse = l.reverse.tail
  | []            := rfl
  | [x]           := rfl
  | (x :: y :: l) := (by simp[init, rev_init_rev_tail]; finish)

  lemma rev_init_rev_tail_2 : Π (l : list α), l.reverse.init = l.tail.reverse :=
  begin
    intros,
    set l2 := l.reverse with l2h,
    calc l.reverse.init = l2.reverse.reverse.init : by rw [l2h,reverse_reverse]
                   ...  = l2.reverse.reverse.init.reverse.reverse : by simp
                   ...  = l2.reverse.reverse.reverse.tail.reverse : by rw rev_init_rev_tail
                   ...  = l.reverse.reverse.tail.reverse : by rw [l2h,reverse_reverse]
                   ...  = l.tail.reverse : by rw reverse_reverse
  end

  lemma rev_init_rev_tail' : Π (l : list α), l.init = l.reverse.tail.reverse := λ l,
  calc l.init = l.init.reverse.reverse : by rw reverse_reverse
          ... = l.reverse.tail.reverse : by rw rev_init_rev_tail

  @[simp] def rev_rel : (α → α → Prop) → (α → α → Prop) := λ S x y, S y x

  lemma chain_rev : Π (L : list α) , chain' R L → chain' (rev_rel R) L.reverse
  | [] h := by simp
  | [x] h := by simp; exact chain.nil
  | (x :: y :: l) h := begin
    rw reverse_cons,
    rw reverse_cons,
    simp,
    apply chain'_split.2,
    rw (reverse_cons y l).symm,
    have h2 : chain' R (y :: l) := (chain_cons.1 h).elim_right,
    split,
    exact chain_rev _ h2,
    apply chain'_of_two.2,
    exact (chain_cons.1 h).elim_left
  end

  lemma chain'_init' : Π (L₁ : list α), chain' R L₁.reverse  → chain' R L₁.reverse.init :=
  begin
    intros,
    rw rev_init_rev_tail',
    apply chain_rev,
    simp,
    cases L₁,
      simp,
    simp,
    have h : chain' (rev_rel R) (L₁_hd :: L₁_tl) := begin
      intros,
      rw (reverse_reverse (L₁_hd :: L₁_tl)).symm,
      exact chain_rev (L₁_hd :: L₁_tl).reverse a,
    end,
    exact chain'_desc_left h
  end

  lemma chain'_init : Π (L₁ : list α), chain' R L₁  → chain' R L₁.init :=
  begin
    intros,
    set L₂ := L₁.reverse with Lh,
    rw (reverse_reverse (L₁)).symm,
    rw Lh.symm,
    apply chain'_init',
    rw Lh,
    rw reverse_reverse,
    assumption
  end

  lemma chain'_trans_last : Π (L : list α) [reflexive R] [transitive R] [chain' R L] (h : L ≠ []), ∀ (x ∈ L), R x (L.last h)
  | [] _ _ _ h := absurd rfl h
  | [x] h _ _ _ := begin
    intros,
    simp,
    rw list.eq_of_mem_singleton H,
    apply h x
  end
  | (x :: y :: l) h₁ h₂ h₃ _ := begin
    intros,
    cases H,
    have I : R x y := chain'_of_first_two h₃,
    have J : R y (last (y :: l) (by simp)) := @chain'_trans_last (y :: l) h₁ h₂ (chain'_desc_left h₃) (by simp) y (by simp),
    have K : R x (last (y :: l) (by simp)) := h₂ I J,
    rw last_cons,
    rw H,
    exact K,
    rw last_cons,
    exact @chain'_trans_last (y :: l) h₁ h₂ (chain'_desc_left h₃) (by simp) x_1 H
  end

  def map₃ : Π (L : list α) (f : Π (a : α), a ∈ L → β), list β
  | [] _ := []
  | (x :: y) f := f x (mem_cons_self x y) :: map₃ y (λ z h, f z (mem_cons_of_mem _ h))

  variables (p : α → Prop) [preorder α]

  def map₄ : Π (L : list α) (f : Π (a : α), a ∈ L → p a), list {x : α // p x}
  | [] _ := []
  | (x :: y) f := ⟨x, f x (mem_cons_self x y)⟩ :: map₄ y (λ z h, f z (mem_cons_of_mem _ h))

  theorem chain'_map₄ : Π (L : list α) (f : Π (a : α), a ∈ L → p a),
    chain' (≤) L → chain' (≤) (map₄ p L (λ a h, (f a h)))
  | [] _ c := (by dunfold map₄; exact (chain'_map (λ (a : {x // p x}), a.val)).mp c)
  | [x] _ c := begin
    intros,
    exact (chain'_map (λ (a : {x // p x}), a.val)).mp c
  end
  | (x :: y :: l) f c := begin
    intros,
    apply chain.cons,
      apply chain'_of_first_two c,
    exact chain'_map₄ (y :: l) (λ z h, f z (mem_cons_of_mem _ h)) (chain'_desc_left c)
  end
    

end list
