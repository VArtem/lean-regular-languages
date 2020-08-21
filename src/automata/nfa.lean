import data.set.basic
import data.fintype.basic
import data.finset.lattice
import tactic

import automata.dfa

namespace nfa
open set list dfa

variables {S Q : Type} [fintype S] [fintype Q] [decidable_eq Q]

structure NFA (S : Type) (Q : Type) [fintype S] [fintype Q] :=
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
    induction left with head tail hyp generalizing a, {
        rintro ⟨_⟩ hbc,
        exact hbc,
    }, {
        rintro (⟨_⟩ | ⟨head, tail, _, nxt, _, h, hab⟩) hbc,
        specialize @hyp nxt,
        exact go.step h (hyp hab hbc),
    }
end

def dfa_to_nfa (dfa : DFA S Q) : NFA S Q := {
    start := dfa.start,
    term := dfa.term,
    next := λ q c, {dfa.next q c}
}

lemma dfa_to_nfa_goes_to
    {d : dfa.DFA S Q} {w : list S} {q r : Q}
    : go (dfa_to_nfa d) q w r ↔ dfa.go d q w r := 
begin
    split, {
        intro go_nfa,
        induction go_nfa with q head tail q nxt f hnxt go_tail ih, {
            exact dfa.go.finish,
        }, {
            suffices : nxt = d.next q head,
            subst this,
            exact dfa.go.step ih,
            simpa only [] using hnxt,
        }
    }, {
        intro go_dfa,
        induction go_dfa with q  head tail q f go_tail ih, {
            exact go.finish,
        }, {
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
        rintro ⟨t, t_go, t_term⟩,
        rw ← dfa_to_nfa_goes_to at t_go,
        use ⟨t, t_go, t_term⟩,
    }, {
        rintro ⟨t, t_go, t_term⟩,
        rw dfa_to_nfa_goes_to at t_go,
        use ⟨t, t_go, t_term⟩,
    }
end

instance [fintype Q] [decidable_eq Q] : decidable_eq (set Q) := sorry

def nfa_to_dfa (nfa : NFA S Q) : DFA S (set Q) := {
    start := {nfa.start},
    term := {q : set Q | by exactI ∃ t, t ∈ q ∧ t ∈ nfa.term },
    next := λ q ch, (⋃ x ∈ q, nfa.next x ch),
}

lemma nfa_to_dfa_subset_subset 
    {n : NFA S Q} {d : dfa.DFA S (set Q)} {s1 s2 e1 e2: set Q} {w : list S} :
    d = nfa_to_dfa n → dfa.go d s1 w e1 → dfa.go d s2 w e2 → (s1 ⊆ s2) → (e1 ⊆ e2) :=
begin
    rintro nfadfa s1e1 s2e2 sub,
    induction w with head tail hyp generalizing s1 s2, {
        cases s1e1,
        cases s2e2,
        exact sub,
    }, {
        rcases s1e1 with _ | ⟨_, _, _, _, s1e1⟩,
        rcases s2e2 with _ | ⟨_, _, _, _, s2e2⟩,
        specialize @hyp (d.next s1 head) (d.next s2 head),
        apply hyp s1e1 s2e2, 
        subst nfadfa, 
        dsimp only [nfa_to_dfa],
        apply bUnion_subset_bUnion_left,
        exact sub,
    }
end

lemma nfa_to_dfa_goes_to
    {n : NFA S Q} {d : dfa.DFA S (set Q)} (w : list S) {S1 E1 : set Q}
    : d = nfa_to_dfa n → dfa.go d S1 w E1 → E1 = {e2 : Q | ∃ (s2 : Q), s2 ∈ S1 ∧ go n s2 w e2} := 
begin
    rintro nfadfa,
    induction w with head tail hyp generalizing S1, {
        rintro ⟨_⟩,
        ext, split, 
        { intro xe1, use [x, xe1, go.finish] },
        { rintro ⟨s2, s2ins1, ⟨s2go⟩⟩, exact s2ins1 },
    }, {
        rintro (⟨_⟩ | ⟨_, _, _, _, h⟩),
        specialize @hyp (d.next S1 head) h,
        rw hyp,
        ext value, split, {
            rintro ⟨s2, s2ins1, s2go⟩,
            subst nfadfa,
            dsimp only [nfa_to_dfa] at *,
            rw mem_bUnion_iff at s2ins1,
            rcases s2ins1 with ⟨x, H, s2innext⟩,
            use [x, H],
            apply go.step s2innext s2go,
        }, {
            rintro ⟨s2, s2ins1, s2go⟩,
            rcases s2go with ⟨_⟩ | ⟨_, _, _, wit, _, witinterm, s2go⟩,
            subst nfadfa,
            dsimp only [nfa_to_dfa] at *,
            use wit,
            rw mem_bUnion_iff,
            use [s2, s2ins1, witinterm],
            exact s2go,
        },
    },
end

theorem nfa_to_dfa_eq {L : set (list S)} (hnfa : nfa_lang L) : dfa_lang L :=
begin
    rcases hnfa with ⟨Q, fQ, dQ, nfa, rfl⟩,
    letI := fQ,
    existsi [set Q, _, _, nfa_to_dfa nfa],    
    ext x,
    dsimp,
    have tmp : (nfa_to_dfa nfa).start = {nfa.start} := rfl,
    rw tmp, clear tmp,

    split, {
        rintro ⟨t, tgo, tterm⟩,
        have tset := dfa.dfa_go_exists_unique (nfa_to_dfa nfa) {nfa.start} x,
        rcases tset with ⟨tset, tseth, tsetuniq⟩,
        use [tset, tseth],
        use t, 
        split, {
            rw nfa_to_dfa_goes_to x rfl tseth,
            use [nfa.start, tgo],
        }, {
            assumption,
        }
    }, {
        rintro ⟨tset, tsetgo, tsetterm⟩,
        dsimp [nfa_to_dfa] at tsetterm,
        rcases tsetterm with ⟨t, ⟨tintset, tinterm⟩⟩,
        use t,
        rw (nfa_to_dfa_goes_to x rfl tsetgo) at tintset,
        rcases tintset with ⟨ns, nssingleton, nfago⟩,
        finish, 
    },
end

end nfa