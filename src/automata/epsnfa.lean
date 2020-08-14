import data.set.basic
import data.fintype.basic
import automata.nfa

open set

namespace epsnfa

variables {S Q : Type} [fintype Q]

structure epsNFA (S : Type) (Q : Type) [fintype Q] :=
    (start : Q) -- starting state
    (term : Q) -- terminal state (only one!)
    (next : Q → S → set Q) -- transitions
    (eps : Q → set Q) -- eps-transitions

inductive go (enfa : epsNFA S Q) : Q → list S → Q → Prop
| finish {q} : go q [] q
| step   : Π {head : S} {tail : list S} {q n f : Q} (h : n ∈ enfa.next q head),
    go n tail f → go q (head::tail) f 
| eps    : Π {tail : list S} {q n f : Q} (h : n ∈ enfa.eps q),
    go n tail f → go q tail f

@[simp] def epsnfa_accepts_word (enfa : epsNFA S Q) (w : list S) : Prop := go enfa enfa.start w enfa.term

def eps_reach (enfa : epsNFA S Q) (q : Q) (r : Q) := go enfa q [] r

@[simp] def lang_of_epsnfa (enfa : epsNFA S Q) := {w | epsnfa_accepts_word enfa w}

def epsnfa_lang (lang : set (list S)) : Prop := 
    ∃ {Q : Type} [fintype Q], by exactI ∃ (enfa : epsNFA S Q), lang_of_epsnfa enfa = lang

lemma epsnfa_go_trans {enfa : epsNFA S Q} {a b c : Q} {left right : list S}:
    go enfa a left b → go enfa b right c → go enfa a (left ++ right) c :=
begin
    rintro hab hfc,
    induction hab with q  head tail q n f h prev ih  tail q n f h prev ih, 
    { exact hfc }, 
    { apply go.step h (ih hfc) },
    { apply go.eps h (ih hfc) },
end

lemma epsnfa_go_exists_cons {enfa : epsNFA S Q} {a d : Q} 
    {head : S} {tail concat : list S} (clr : list.cons head tail = concat):
    go enfa a concat d → (∃ {b c : Q}, eps_reach enfa a b ∧ c ∈ enfa.next b head ∧ go enfa c tail d) :=
begin
    intros go_ac,
    induction go_ac with q  head tail q n f h prev ih  tail q n f h prev ih, {
        contradiction,
    }, {
        rw list.cons.inj_eq at clr,
        rcases clr with ⟨rfl, rfl⟩,
        use [q, n, go.finish, h, prev],
    }, {
        rcases ih clr with ⟨b, c, eps_ab, next_bc, tail_cd⟩,
        use [b, c, go.eps h eps_ab, next_bc, tail_cd],
    }
end

lemma epsnfa_go_exists_trans {enfa : epsNFA S Q} {a c : Q} 
    {left right concat : list S} (clr : left ++ right = concat):
    go enfa a concat c → (∃ {b : Q}, go enfa a left b ∧ go enfa b right c) :=
begin
    intros go_ac,
    induction left with head tail ih generalizing a concat, {
        subst clr,
        use [a, go.finish, go_ac],
    }, {
        subst clr,
        rcases epsnfa_go_exists_cons rfl go_ac with ⟨b, c', eps_ab, next_bc', tail_cd⟩,
        specialize @ih c' (tail ++ right) rfl,
        rcases ih tail_cd with ⟨real_b, go_real_b_tail, go_real_b_right⟩,

        use [real_b],
        use [epsnfa_go_trans eps_ab (go.step next_bc' go_real_b_tail)],
        use [go_real_b_right],
    }
end

section epsnfa_to_nfa

def epsnfa_to_nfa (enfa : epsNFA S Q) : nfa.NFA S Q := {
    start := enfa.start,
    term := {x | eps_reach enfa x enfa.term},
    next := λ q c, {y | ∃ x, eps_reach enfa q x ∧ y ∈ enfa.next x c}
}

lemma epsnfa_to_nfa_accepts_iff_accepts
    (en : epsNFA S Q) {n : nfa.NFA S Q} (w : list S) (st : Q)
    : n = epsnfa_to_nfa en → (go en st w en.term ↔ ∃ t : Q, nfa.go n st w t ∧ t ∈ n.term) :=
begin
    rintro enfa_nfa,
    split, {
        rintro en_go,
        induction w with head tail hyp generalizing st, {
            use [st, nfa.go.finish],
            rw enfa_nfa,
            dsimp [epsnfa_to_nfa],
            use en_go,
        }, {
            replace en_go := epsnfa_go_exists_cons rfl en_go,
            rcases en_go with ⟨b, c, eps_stb, next_bc, tail_cent⟩,
            specialize hyp c tail_cent,
            rcases hyp with ⟨t, t_go, t_term⟩,
            use t,
            split, { 
                refine nfa.go.step _ t_go, 
                rw enfa_nfa, 
                dsimp [epsnfa_to_nfa],
                use [b, eps_stb, next_bc],
            },
            exact t_term,
        }
    }, {
        rintro ⟨n_t, n_go, n_term⟩,
        rw enfa_nfa at n_term,
        dsimp [epsnfa_to_nfa] at n_term,
        induction w with head tail hyp generalizing st, {
            cases n_go,
            use n_term,
        }, {
            cases n_go,
            specialize hyp n_go_n n_go_a,
            rw [enfa_nfa] at n_go_h, 
            rcases n_go_h with ⟨x, x_go, x_next⟩,
            exact epsnfa_go_trans x_go (go.step x_next hyp),
        }     
    }    
end

theorem epsnfa_to_nfa_eq {L : set (list S)} : epsnfa_lang L → nfa.nfa_lang L :=
begin
    rintro ⟨Q, fQ, enf, rfl⟩,
    letI := fQ,
    existsi [Q, _, epsnfa_to_nfa enf],
    ext x,
    exact epsnfa_to_nfa_accepts_iff_accepts enf x enf.start rfl,    
end

theorem epsnfa_to_dfa_eq {L : set (list S)} : epsnfa_lang L → dfa.dfa_lang L := nfa.nfa_to_dfa_eq ∘ epsnfa_to_nfa_eq

end epsnfa_to_nfa

section nfa_to_epsnfa

inductive U (Q : Type) : Type
| inside : Q → U
| finish : U

instance [fintype Q] : fintype (U Q) := sorry

def nfa_to_epsnfa (nfa : nfa.NFA S Q) : epsNFA S (U Q) := {
    start := U.inside nfa.start,
    term := U.finish,
    next := λ q c, begin
        cases q,
        exact U.inside '' nfa.next q c,
        exact ∅,
    end,
    eps := λ q, begin
        cases q,
        by_cases q ∈ nfa.term,
        exact {U.finish},
        exact ∅,
        exact ∅,
    end,
}

lemma nfa_to_epsnfa_accepts_iff_accepts
    (n : nfa.NFA S Q) {en : epsNFA S (U Q)} (w : list S) (st : Q)
    : en = nfa_to_epsnfa n → (go en (U.inside st) w U.finish  ↔ ∃ t : Q, nfa.go n st w t ∧ t ∈ n.term) :=
begin
    rintro rfl,
    split, {
        intro go_enfa,
        generalize hst : U.inside st = ust,
        generalize hfi : (U.finish : U Q) = ufi,
        rw [hst, hfi] at go_enfa,
        induction go_enfa generalizing st, {
            subst hfi,
            injection hst,
        }, {
            substs hst hfi,
            cases go_enfa_n, {
                specialize go_enfa_ih rfl go_enfa_n rfl,
                rcases go_enfa_ih with ⟨t, t_go, t_term⟩,
                simp [nfa_to_epsnfa] at go_enfa_h,
                use [t, nfa.go.step go_enfa_h t_go, t_term],
            }, {
                simpa [nfa_to_epsnfa] using go_enfa_h,
            }
        }, {
            substs hst hfi,
            cases go_enfa_n, {
                by_cases st ∈ n.term;
                simpa [nfa_to_epsnfa, h] using go_enfa_h,
            }, {
                by_cases st ∈ n.term, {
                    suffices tail_nil : go_enfa_tail = [],
                    subst tail_nil, 
                    use [st, nfa.go.finish, h],
                    cases go_enfa_a, 
                    { refl, },
                    { simpa [nfa_to_epsnfa] using go_enfa_a_h, },
                    { simpa [nfa_to_epsnfa] using go_enfa_a_h, },
                }, {
                    simpa [nfa_to_epsnfa, h] using go_enfa_h,
                }
            }
        }
    }, {
        rintro ⟨t, t_go, t_term⟩,
        induction t_go, {
            refine go.eps _ go.finish,
            simp [nfa_to_epsnfa, t_term], 
        }, {
            refine go.step _ (t_go_ih t_term),
            simpa [nfa_to_epsnfa],
        },
    }
end

theorem nfa_to_epsnfa_eq {L : set (list S)} : nfa.nfa_lang L → epsnfa_lang L :=
begin
    rintro ⟨Q, fQ, nfa, rfl⟩,
    letI := fQ,
    existsi [U Q, _, nfa_to_epsnfa nfa],
    ext x,
    exact nfa_to_epsnfa_accepts_iff_accepts nfa x nfa.start rfl,
end

theorem dfa_to_epsnfa_eq {L : set (list S)} : dfa.dfa_lang L → epsnfa_lang L := nfa_to_epsnfa_eq ∘ nfa.dfa_to_nfa_eq

end nfa_to_epsnfa

end epsnfa