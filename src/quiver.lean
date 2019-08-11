import set_theory.zfc
import data.vector
import order.lattice
import order.complete_lattice

import .lists
import .downset

class quiver :=
    (vertices : Type)
    (edges : Type)
    (s : edges → vertices)
    (t : edges → vertices)

namespace quiver

    def head_to_head {Q : quiver} : Q.edges → Q.edges → Prop := 
      λ e₁ e₂, quiver.t e₁ = quiver.s e₂

    variable (Q : quiver)
    
    structure path := 
      (start : Q.vertices)
      (edges : list Q.edges)
      (h2h : list.chain' head_to_head edges)
      [st : Π h : edges ≠ [], quiver.s (list.head'' edges h) = start]
    
    namespace path
    
      variables {Q}
      
      def end' (p : path Q) : Q.vertices := 
        list.rec_on p.edges p.start (λ h t r, quiver.t (list.last ( h :: t ) (by simp) ))

      lemma empty_path_start_is_end (p : path Q) : p.edges = [] → p.end' = p.start :=
      begin
        intros,
        dunfold end',
        cases p.edges,
        simp,
        contradiction
      end
    
    end path

    def is_path_between (a b : Q.vertices) : Prop := 
      ∃ (p : path Q), p.start = a ∧ p.end' = b

    def concatenate (p q : path Q) : p.end' = q.start → path Q := λ h₁, {
      start := p.start,
      edges := p.edges ++ q.edges,
      h2h := begin
        intros,
        rcases p,
        rcases q,
          simp,
          rcases q_edges,      
            simp,
            assumption,
          rcases p_edges,
            simp,
            assumption,
        /- ⊢ list.chain' head_to_head (p_edges_hd :: p_edges_tl ++ q_edges_hd :: q_edges_tl) -/  
        apply list.chain'_concat' ⟨p_edges_hd :: p_edges_tl, (by simp)⟩ ⟨q_edges_hd :: q_edges_tl, (by simp)⟩ _ p_h2h q_h2h,
        /- ⊢ head_to_head (nonempty_list.last ⟨p_edges_hd :: p_edges_tl, _⟩)
                          (nonempty_list.head ⟨q_edges_hd :: q_edges_tl, _⟩) -/
        simp,
        dunfold head_to_head,
        have k : s q_edges_hd = q_start := q_st (by simp),
        have i : t (list.last (p_edges_hd :: p_edges_tl) _) = path.end' (@path.mk Q p_start  (p_edges_hd :: p_edges_tl) p_h2h p_st) := rfl,
        rw k,
        rw i,
        assumption
      end,
      st := sorry
    }

    lemma concat_ends (p q : path Q) (h : p.end' = q.start) : (concatenate Q p q h).end' = q.end' := sorry
    lemma concat_starts (p q : path Q) (h : p.end' = q.start) : (concatenate Q p q h).start = p.start := (by intros; dunfold concatenate; simp)

    variable {Q}

    def zero_length_path (a : Q.vertices) : path Q := {
      start := a,
      edges := [],
      h2h := by trivial,
      st := by simp
    }

    @[simp]
    lemma zero_length_path_ends (a : Q.vertices) : (zero_length_path a).end' = a := by trivial

    @[simp]
    def is_arrow_closed (S : set Q.vertices) : Prop := 
        ∀ (e : Q.edges), s(e) ∈ S → t(e) ∈ S
end quiver

variables (Q : quiver)

class is_acyclic :=
  (no_cycle : ∀ a b, quiver.is_path_between Q a b → quiver.is_path_between Q b a → a = b)

instance quiver_vertices_partial [h : is_acyclic Q] : partial_order Q.vertices := {
  le := quiver.is_path_between Q,
  le_refl := λ a, ⟨ quiver.zero_length_path a, ⟨ rfl , quiver.zero_length_path_ends a ⟩ ⟩,
  le_trans := λ a b c, λ p₁ p₂, exists.elim p₂ (exists.elim p₁ (
    begin
      intros;
      simp;
      exact ⟨ quiver.concatenate Q a_1 a_3 (begin transitivity b; simp[a_2,a_4] end ) , (begin rw quiver.concat_ends Q a_1 a_3 _; rw quiver.concat_starts Q a_1 a_3; exact ⟨ and.elim_left a_2 , and.elim_right a_4 ⟩ end) ⟩
    end
  )) ,
  le_antisymm := h.no_cycle
  }