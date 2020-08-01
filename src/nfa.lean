import data.set.basic
import data.set.finite
import dfa

namespace nfa
open set
open dfa

structure NFA (S : Type) (Q : Type) :=
    (start : Q) -- starting state
    (term : Q → Prop) -- terminal states
    (next : Q → S → set Q) -- transitions

def nfa_goes_to {S Q : Type} (nfa : NFA S Q) : Q → list S → set Q
| q []              := {q}
| q (head :: tail)  := ⋃₀ { S : set Q | 
    ∃ {t : Q}, t ∈ (nfa.next q head) ∧ S = nfa_goes_to t tail }


@[simp] def nfa_accepts_word {S Q : Type} (nfa : NFA S Q) (w : list S) : Prop := 
    ∃ t : Q, nfa.term t ∧ t ∈ nfa_goes_to nfa nfa.start w

def lang_of_nfa {S Q : Type} (nfa : NFA S Q) :=
    { w : list S | nfa_accepts_word nfa w}

def nfa_lang {S : Type} (lang : set (list S)) : Prop := 
    ∃ {Q : Type} (aut : NFA S Q), lang = lang_of_nfa aut

theorem dfa_to_nfa {S : Type} {L : set (list S)} (hdfa : dfa_lang L) : nfa_lang L :=
begin
    rcases hdfa with ⟨ Q, dfa, hdfa⟩,
    use Q,
    use {
        start := dfa.start,
        term := dfa.term,
        next := λ q, λ c, {dfa.next q c}
    },
    ext,
    split,
    {
        intro xl,
        dsimp [lang_of_nfa],
        rw word_in_lang_iff_dfa_goes_to_term hdfa at xl,
        use dfa_goes_to dfa dfa.start x,
        use xl,
        sorry,       
    },
    {
        sorry,
    },
end

end nfa