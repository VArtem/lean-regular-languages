import data.set.basic
import data.fintype.basic
import data.finset.basic
import tactic

import automata.dfa

namespace nfa
open set list DFA finset

variables {S Q : Type} [fintype S] [fintype Q] [decidable_eq Q]

structure NFA (S : Type) (Q : Type) [fintype S] [fintype Q] [decidable_eq Q] :=
    (start : Q) -- starting state
    (term : set Q) -- terminal states
    (next : Q → S → set Q) -- transitions

inductive go (nfa : NFA S Q) : Q → list S → Q → Prop
| finish : Π {q : Q}, go q [] q
| step   : Π {head : S} {tail : list S} {q n f : Q} (h : n ∈ nfa.next q head),
    go n tail f → go q (head::tail) f 

@[simp] def nfa_accepts_word (nfa : NFA S Q) (w : list S) : Prop := 
    ∃ {t}, go nfa nfa.start w t ∧ t ∈ nfa.term

@[simp] def lang_of_nfa (nfa : NFA S Q) := {w | nfa_accepts_word nfa w}

def nfa_lang (lang : set (list S)) :=
    ∃ {Q : Type} [fintype Q] [decidable_eq Q], by exactI ∃ (nfa : NFA S Q), lang = lang_of_nfa nfa

lemma nfa_go_append {nfa : NFA S Q} {a b c : Q} {left right : list S}:
    go nfa a left b → go nfa b right c → go nfa a (left ++ right) c :=
begin
    induction left generalizing a, 
    case list.nil : {
        rintro ⟨_⟩ hbc,
        exact hbc,
    }, 
    case list.cons : head tail ih {
        rintro (⟨_⟩ | ⟨head, tail, _, nxt, _, h, hab⟩) hbc,
        specialize @ih nxt,
        exact go.step h (ih hab hbc),
    }
end

def dfa_to_nfa (dfa : DFA S Q) : NFA S Q := {
    start := dfa.start,
    term := dfa.term,
    next := λ q c, {dfa.next q c}
}

lemma dfa_to_nfa_goes_to
    {d : DFA S Q} {w : list S} {q r : Q}
    : go (dfa_to_nfa d) q w r ↔ DFA.go d q w = r := 
begin
    split, {
        intro go_nfa,
        induction go_nfa, 
        case nfa.go.finish {
            rw DFA.go_finish,
        }, 
        case nfa.go.step : head tail q nxt f hnxt go_tail ih {
            rw DFA.go_step,
            convert ih,
            simp only [dfa_to_nfa, mem_singleton_iff] at hnxt,
            exact hnxt.symm,
        }
    }, {
        intro go_dfa,
        induction w generalizing q, 
        case list.nil {
            cases go_dfa, exact go.finish,
        }, 
        case list.cons : head tail ih {
            cases go_dfa,
            specialize @ih (d.next q head) go_dfa,
            refine go.step _ ih,
            simp only [dfa_to_nfa, set.mem_singleton],
        }
    }
end

theorem dfa_to_nfa_eq {L : set (list S)} (hdfa : dfa_lang L) : nfa_lang L :=
begin
    rcases hdfa with ⟨Q, fQ, dQ, d, rfl⟩,
    letI := fQ,
    existsi [Q, _, _, dfa_to_nfa d],
    
    ext x,
    rw [lang_of_dfa, lang_of_nfa, mem_set_of_eq, mem_set_of_eq],
    split, {
        rintro dfa_go,
        dsimp at dfa_go,
        use [DFA.go d (d.start) x],
        rw dfa_to_nfa_goes_to,
        use [rfl, dfa_go],        
    }, {
        rintro ⟨t, t_go, t_term⟩,
        rw dfa_to_nfa_goes_to at t_go,
        subst t_go,
        use t_term,
    }
end


noncomputable def nfa_to_dfa (nfa : NFA S Q) : DFA S (set Q) := {
    start := {nfa.start},
    term := {q | ∃ t, t ∈ q ∧ t ∈ nfa.term},
    next := λ q c, (⋃ t ∈ q, nfa.next t c),
}

lemma nfa_to_dfa_goes_to
    {n : NFA S Q} {d : DFA S (set Q)} (w : list S) {S1 : set Q}
    : d = nfa_to_dfa n → DFA.go d S1 w = {e2 : Q | ∃ (s2 : Q), s2 ∈ S1 ∧ go n s2 w e2} := 
begin
    rintro rfl,
    induction w with head tail ih generalizing S1, {
        ext, split, 
        { intro xe1, use [x, xe1, go.finish] },
        { rintro ⟨s2, s2ins1, ⟨s2go⟩⟩, exact s2ins1 },
    }, {
        specialize @ih ((nfa_to_dfa n).next S1 head),
        ext value, split, {
            intro dfa_go,
            rw [go_step, ih] at dfa_go,
            rcases dfa_go with ⟨s2, s2innext, s2go⟩,
            rw [nfa_to_dfa, mem_bUnion_iff] at s2innext,
            rcases s2innext with ⟨x, x_in_s1, x_next⟩,
            use [x, x_in_s1, go.step x_next s2go],
        }, {
            rintro ⟨s2, s2ins1, s2go⟩,
            rw [DFA.go_step, ih],
            cases s2go,
            use s2go_n,
            split, {
                dsimp [nfa_to_dfa],
                rw mem_bUnion_iff,
                use [s2, s2ins1, s2go_h],
            }, {
                assumption,
            }
        },
    },
end

theorem nfa_to_dfa_eq {L : set (list S)} (hnfa : nfa_lang L) : dfa_lang L :=
begin
    rcases hnfa with ⟨Q, fQ, dQ, nfa, rfl⟩,
    letI := fQ,
    existsi [set Q, _, _, nfa_to_dfa nfa],    
    ext x,
    split, {
        rintro ⟨tset, tsetgo, tsetterm⟩,
        use tset,
        rw (nfa_to_dfa_goes_to x rfl),
        simp,
        use [nfa.start],
        simp [nfa_to_dfa, tsetgo],
        exact tsetterm,
    }, {
        rintro ⟨tset, tsetgo, tsetterm⟩,
        simp only [nfa_to_dfa_goes_to x rfl, mem_set_of_eq] at tsetgo,
        rcases tsetgo with ⟨s2, s2start, s2go⟩,
        use [tset],
        simp [nfa_to_dfa] at s2start,
        subst s2start,
        use [s2go, tsetterm],
    },
end

end nfa