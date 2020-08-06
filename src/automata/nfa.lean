import data.set.basic
import data.set.finite
import tactic

import automata.dfa

namespace nfa
open set list dfa

variables {S Q : Type}

structure NFA (S : Type) (Q : Type) :=
    (start : Q) -- starting state
    (term : set Q) -- terminal states
    (next : Q → S → set Q) -- transitions

inductive go (nfa : NFA S Q) : Q → list S → Q → Prop
| finish : Π {q : Q}, go q [] q
| step   : Π {head : S} {tail : list S} {q n f : Q} (h : n ∈ nfa.next q head),
    go n tail f → go q (head::tail) f 

@[simp] def nfa_accepts_word (nfa : NFA S Q) (w : list S) : Prop := 
    ∃ {t}, go nfa nfa.start w t ∧ t ∈ nfa.term

@[simp] def lang_of_nfa (nfa : NFA S Q) :=
    { w : list S | nfa_accepts_word nfa w}

def nfa_lang (lang : set (list S)) : Prop := 
    ∃ {Q : Type} (aut : NFA S Q), lang = lang_of_nfa aut

def dfa_to_nfa (dfa : DFA S Q) : NFA S Q := {
    start := dfa.start,
    term := dfa.term,
    next := λ q, λ c, {dfa.next q c}
}

@[simp] lemma nfa_go_step_iff (nfa : NFA S Q) (q r : Q) {head : S} {tail : list S} :
    go nfa q (head :: tail) r ↔ ∃ {t : Q}, (t ∈ nfa.next q head) ∧ (go nfa t tail r) :=
begin
    split,
    { rintro (⟨_⟩ | ⟨ head, tail, q, n, f, h, prev⟩), use [n, h, prev] }, 
    { rintro ⟨t, ht, tgo⟩, apply go.step ht tgo }, 
end

lemma dfa_to_nfa_goes_to
    {d : dfa.DFA S Q} {n : NFA S Q} (w : list S) (q : Q)
    : (n = dfa_to_nfa d) → (go n q w = dfa.go d q w) := 
begin
    rintro ⟨ rfl ⟩,
    induction w with head tail hyp generalizing q,
    {
        dsimp [dfa_to_nfa] at *,
        ext, split,
        { rintro ⟨_⟩, exact dfa.go.finish },
        { rintro ⟨_⟩, exact nfa.go.finish },
    },
    {
        specialize hyp (d.next q head),
        rw dfa.dfa_go_step_iff,
        ext, split,
        {
            rintro (⟨_⟩ | ⟨ head, tail, q, nxt, f, h, prev⟩),
            rw ← hyp,
            convert prev,
            rw mem_singleton_iff at h,
            use h.symm
        },
        {
            intro h,
            apply go.step,
            rw [mem_singleton_iff],
            rw hyp,
            exact h,
        }
    },
end


theorem dfa_to_nfa_eq {L : set (list S)} (hdfa : dfa_lang L) : nfa_lang L :=
begin
    rcases hdfa with ⟨ Q, d, rfl⟩,
    use Q,
    use dfa_to_nfa d,
    ext x,
    rw [lang_of_dfa, lang_of_nfa, mem_set_of_eq, mem_set_of_eq],
    rw [dfa_accepts_word, nfa_accepts_word],
    
    have tmp : (dfa_to_nfa d).start = d.start := rfl,
    rw tmp,
    have tmp2 := @dfa_to_nfa_goes_to S Q d (dfa_to_nfa d) x d.start rfl,
    rw tmp2,
    finish, 
end


def nfa_to_dfa (nfa : NFA S Q) : DFA S (set Q) := {
    start := {nfa.start},
    term := {q : set Q | (q ∩ nfa.term).nonempty},
    next := λ q ch, (⋃ x ∈ q, nfa.next x ch),
}


lemma nfa_to_dfa_subset_subset {n : NFA S Q} {d : dfa.DFA S (set Q)} {s1 s2 e1 e2: set Q} {w : list S} :
    (d = nfa_to_dfa n) → dfa.go d s1 w e1 → dfa.go d s2 w e2 → (s1 ⊆ s2) → (e1 ⊆ e2) :=
begin
    rintro nfadfa s1e1 s2e2 sub,
    induction w with head tail hyp generalizing s1 s2,
    {
        cases s1e1,
        cases s2e2,
        exact sub,
    },
    {
        cases s1e1,
        cases s2e2,
        specialize @hyp (d.next s1 head) (d.next s2 head),
        apply hyp,
        assumption, assumption,
        rw nfadfa, 
        dsimp [nfa_to_dfa],
        apply bUnion_subset_bUnion_left,
        exact sub,
    }
end

lemma nfa_to_dfa_goes_to
    {n : NFA S Q} {d : dfa.DFA S (set Q)} (w : list S) {S1 E1 : set Q}
    : (d = nfa_to_dfa n) → dfa.go d S1 w E1 → E1 = {e2 : Q | ∃ (s2 : Q), s2 ∈ S1 ∧ go n s2 w e2} := 
begin
    rintro nfadfa,
    induction w with head tail hyp generalizing S1,
    {
        intro s1e1,
        cases s1e1,
        ext, split,
        {
            intro xe1,
            dsimp,
            use [x, xe1, go.finish], 
        },
        {
            dsimp,
            rintro ⟨s2, s2ins1, s2go⟩,
            cases s2go,
            exact s2ins1,
        }
    },
    {
        rintro (⟨_⟩ | ⟨head, tail, _, _, h⟩),
        specialize @hyp (d.next S1 head) h,
        rw hyp,
        ext value, dsimp, split,
        {
            rintro ⟨s2, s2ins1, s2go⟩,
            rw [nfadfa, nfa_to_dfa] at s2ins1,
            rw mem_bUnion_iff at s2ins1,
            rcases s2ins1 with ⟨ x, H, s2innext⟩,
            use [x, H],
            apply go.step s2innext s2go,
        },
        {
            rintro ⟨s2, s2ins1, s2go⟩,
            rcases s2go with ⟨_⟩ | ⟨_, _, _, wit, _, witinterm, s2go⟩,
            use wit,
            split,
            rw [nfadfa],
            dsimp [nfa_to_dfa],
            rw mem_bUnion_iff,
            use [s2, s2ins1, witinterm],
            exact s2go,            
        },
    },
end

theorem nfa_to_dfa_eq {L : set (list S)} (hnfa : nfa_lang L) : dfa_lang L :=
begin
    rcases hnfa with ⟨ Q, n, rfl⟩,
    use [set Q, nfa_to_dfa n],
    ext x,
    rw [lang_of_dfa, lang_of_nfa, mem_set_of_eq, mem_set_of_eq],
    rw [dfa_accepts_word, nfa_accepts_word],
    have tmp : {n.start} = (nfa_to_dfa n).start := rfl,
    rw ← tmp,
    clear tmp,
    
    split,
    {
        rintro ⟨ t, tgo, tterm ⟩,
        have tset := dfa.dfa_go_exists_unique (nfa_to_dfa n) {n.start} x,
        rcases tset with ⟨tset, tseth, tsetuniq⟩,
        clear tsetuniq,
        use [tset, tseth],
        dsimp [nfa_to_dfa],
        use t, 
        split, {
            have tmp := nfa_to_dfa_goes_to x (rfl : nfa_to_dfa n = nfa_to_dfa n) tseth,
            rw tmp,
            dsimp,
            use n.start,
            simp,
            use tgo,
        }, {
            assumption,
        }
    },
    {
        rintro ⟨ tset, tsetgo, tsetterm ⟩,
        dsimp [nfa_to_dfa] at tsetterm,
        rcases tsetterm with ⟨t, ⟨tintset, tinterm⟩⟩,
        use t,
        have tmp := nfa_to_dfa_goes_to x (rfl : nfa_to_dfa n = nfa_to_dfa n) tsetgo,
        rw tmp at tintset,
        dsimp [tmp] at tintset,
        rcases tintset with ⟨ns, nstartsing, nfago⟩,
        rw [mem_singleton_iff] at nstartsing,
        subst nstartsing,
        use nfago, 
        assumption,
    },
end

end nfa