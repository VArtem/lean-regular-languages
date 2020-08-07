import data.set.basic
import data.set.finite
import automata.nfa

open set

namespace epsnfa

variables {S Q : Type}

structure epsNFA (S : Type) (Q : Type) :=
    (start : Q) -- starting state
    (term : set Q) -- terminal states
    (next : Q → S → set Q) -- transitions
    (eps : Q → set Q) -- eps-transitions

inductive go (enfa : epsNFA S Q) : Q → list S → Q → Prop
| finish : Π {q : Q}, go q [] q
| step   : Π {head : S} {tail : list S} {q n f : Q} (h : n ∈ enfa.next q head),
    go n tail f → go q (head::tail) f 
| eps    : Π {tail : list S} {q n f : Q} (h : n ∈ enfa.eps q),
    go n tail f → go q tail f

@[simp] def epsnfa_accepts_word (enfa : epsNFA S Q) (w : list S) : Prop := 
    ∃ {t}, go enfa enfa.start w t ∧ t ∈ enfa.term

def eps_reach (enfa : epsNFA S Q) (q : Q) (r : Q) := go enfa q [] r

@[simp] def lang_of_epsnfa (enfa : epsNFA S Q) := {w | epsnfa_accepts_word enfa w}

def epsnfa_lang (lang : set (list S)) : Prop := 
    ∃ {Q : Type} (enfa : epsNFA S Q), lang = lang_of_epsnfa enfa

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

def epsnfa_to_nfa (enfa : epsNFA S Q) : nfa.NFA S Q := {
    start := enfa.start,
    term := {x | ∃ t, eps_reach enfa x t ∧ t ∈ enfa.term},
    next := λ q c, {y | ∃ x, eps_reach enfa q x ∧ y ∈ enfa.next x c}
}

lemma epsnfa_to_nfa_accepts_iff_accepts
    (en : epsNFA S Q) {n : nfa.NFA S Q} (w : list S) (st : Q)
    : n = epsnfa_to_nfa en → ((∃ t : Q, go en st w t ∧ t ∈ en.term) ↔ (∃ t : Q, nfa.go n st w t ∧ t ∈ n.term)) :=
begin
    rintro enfa_nfa,
    split, {
        rintro ⟨en_t, en_go, en_tterm⟩,
        induction w with head tail hyp generalizing st, {
            use [st, nfa.go.finish],
            rw enfa_nfa,
            dsimp [epsnfa_to_nfa],
            use [en_t, en_go, en_tterm], 
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
        rcases n_term with ⟨en_t, en_t_eps, en_t_term⟩,
        induction w with head tail hyp generalizing st, {
            cases n_go, 
            use [en_t, en_t_eps, en_t_term],
        }, {
            cases n_go,
            specialize hyp n_go_n n_go_a,
            rcases hyp with ⟨t, t_go, t_term⟩,
            rw [enfa_nfa] at n_go_h, 
            rcases n_go_h with ⟨x, x_go, x_next⟩,
            use [t, and.intro (epsnfa_go_trans x_go (go.step x_next t_go)) t_term],
        }     
    }    
end

theorem epsnfa_to_nfa_eq {L : set (list S)} : epsnfa_lang L → nfa.nfa_lang L :=
begin
    rintro ⟨Q, enf, rfl⟩,
    use [Q, epsnfa_to_nfa enf],
    ext x,
    convert epsnfa_to_nfa_accepts_iff_accepts enf x enf.start rfl,    
end

end epsnfa