import data.set.basic
import data.set.finite
import dfa

open set dfa

namespace nfa

variables {S Q : Type}

structure NFA (S : Type) (Q : Type) :=
    (start : Q) -- starting state
    (term : set Q) -- terminal states
    (next : Q → S → set Q) -- transitions

@[simp] def nfa_goes_to (nfa : NFA S Q) : set Q → list S → set Q
| q []              := q
| q (head :: tail)  := nfa_goes_to (⋃ t ∈ q, nfa.next t head) tail

@[simp] def nfa_accepts_word (nfa : NFA S Q) (w : list S) : Prop := 
    ∃ t : Q, t ∈ nfa.term ∧ t ∈ nfa_goes_to nfa {nfa.start} w

@[simp] def lang_of_nfa (nfa : NFA S Q) :=
    { w : list S | nfa_accepts_word nfa w}

def nfa_lang (lang : set (list S)) : Prop := 
    ∃ {Q : Type} (aut : NFA S Q), lang = lang_of_nfa aut

def dfa_to_nfa (dfa : DFA S Q) : NFA S Q := {
    start := dfa.start,
    term := dfa.term,
    next := λ q, λ c, {dfa.next q c}
}

lemma dfa_to_nfa_goes_to
    {dfa : DFA S Q} {nfa : NFA S Q} (w : list S) (q : Q)
    : (nfa = dfa_to_nfa dfa) → nfa_goes_to nfa {q} w = {dfa_goes_to dfa q w} := 
begin
    rintro rfl,
    induction w with head tail hyp generalizing q,
    {
        simp [dfa_goes_to], 
    },
    {
        rw [nfa_goes_to, dfa_goes_to],
        rw bUnion_singleton,
        specialize @hyp (dfa.next q head),
        have t : (dfa_to_nfa dfa).next q head = {dfa.next q head} := rfl,
        rw t,
        exact hyp,  
    },
end


theorem dfa_to_nfa_eq {L : set (list S)} (hdfa : dfa_lang L) : nfa_lang L :=
begin
    rcases hdfa with ⟨ Q, dfa, rfl⟩,
    use Q,
    use dfa_to_nfa dfa,
    ext x,
    rw [lang_of_dfa, lang_of_nfa, mem_set_of_eq, mem_set_of_eq],
    rw [dfa_accepts_word, nfa_accepts_word],
    
    have tmp : (dfa_to_nfa dfa).start = dfa.start := rfl,
    rw tmp,
    have tmp2 := @dfa_to_nfa_goes_to S Q dfa (dfa_to_nfa dfa) x dfa.start rfl,
    rw tmp2,
    split,
    {  
        intro hterm, 
        use dfa_goes_to dfa dfa.start x,
        simpa only [and_true, mem_singleton], 
    },
    {
        rintro ⟨t, h1, h2⟩,
        finish,
    }
end


def nfa_to_dfa (nfa : NFA S Q) : DFA S (set Q) := {
    start := {nfa.start},
    term := {q : set Q | (q ∩ nfa.term).nonempty},
    next := λ q s, (⋃ x ∈ q, nfa.next x s) 
}

lemma nfa_to_dfa_goes_to
    {nfa : NFA S Q} {dfa : DFA S (set Q)} (w : list S) (q : set Q)
    : (dfa = nfa_to_dfa nfa) → dfa_goes_to dfa q w = nfa_goes_to nfa q w := 
begin
    rintro rfl,
    induction w with head tail hyp generalizing q,
    {
        simp [dfa_goes_to],
    },
    {
        rw [nfa_goes_to, dfa_goes_to],
        specialize @hyp (⋃ t ∈ q, nfa.next t head),
        have t : (nfa_to_dfa nfa).next q head = (⋃ t ∈ q, nfa.next t head) := rfl,
        rw t,
        clear t,
        convert hyp,
    }
end

theorem nfa_to_dfa_eq {L : set (list S)} (hnfa : nfa_lang L) : dfa_lang L :=
begin
    rcases hnfa with ⟨ Q, nfa, rfl⟩,
    use [set Q, nfa_to_dfa nfa],
    ext x,
    rw [lang_of_dfa, lang_of_nfa, mem_set_of_eq, mem_set_of_eq],
    rw [dfa_accepts_word, nfa_accepts_word],
    have tmp : {nfa.start} = (nfa_to_dfa nfa).start := rfl,
    rw ← tmp,
    have tmp2 := @nfa_to_dfa_goes_to S Q nfa (nfa_to_dfa nfa) x {nfa.start} rfl,
    rw tmp2,
    split,
    {  
        rintro ⟨t, ⟨hterm, hgoes⟩⟩,
        dsimp [nfa_to_dfa],
        use [t, hgoes, hterm],
    },
    {
        rintro ⟨t, h1, h2⟩,
        finish,
    }
end

end nfa