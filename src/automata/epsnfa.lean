import data.set.basic
import data.fintype.basic
import automata.nfa

open set

namespace epsnfa

structure epsNFA (S : Type) (Q : Type) [fintype Q] [decidable_eq Q] :=
    (start : Q) -- starting state
    (term : Q) -- terminal state (only one!)
    (next : Q → S → set Q) -- transitions
    (eps : Q → set Q) -- eps-transitions

variables {S Q : Type} [fintype S] [fintype Q] [decidable_eq Q] {enfa : epsNFA S Q}

inductive go (enfa : epsNFA S Q) : Q → list S → Q → Prop
| finish {q} : 
    go q [] q
| step {hd tl q n f} (h : n ∈ enfa.next q hd) :
    go n tl f → 
    go q (hd::tl) f 
| eps {tl q n f} (h : n ∈ enfa.eps q):
    go n tl f → go q tl f

@[simp] def epsnfa_accepts_word (enfa : epsNFA S Q) (w : list S) := go enfa enfa.start w enfa.term

def eps_reach (enfa : epsNFA S Q) (q : Q) (r : Q) := go enfa q [] r

@[simp] def lang_of_epsnfa (enfa : epsNFA S Q) := {w | epsnfa_accepts_word enfa w}

@[simp] def mem_of_epsnfa_iff {w} : w ∈ lang_of_epsnfa enfa ↔ go enfa enfa.start w enfa.term := by refl

def epsnfa_lang (lang : set (list S)) : Prop := 
    ∃ {Q : Type} [fintype Q] [decidable_eq Q], by exactI ∃ (enfa : epsNFA S Q), lang_of_epsnfa enfa = lang

lemma epsnfa_go_trans {a b c : Q} {left right : list S}:
    go enfa a left b → go enfa b right c → go enfa a (left ++ right) c :=
begin
    rintro hab hfc,
    induction hab with q  head tail q n f h prev ih  tail q n f h prev ih, 
    { exact hfc }, 
    { apply go.step h (ih hfc) },
    { apply go.eps h (ih hfc) },
end

lemma epsnfa_go_exists_cons {a d : Q} 
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

lemma epsnfa_go_exists_trans {a c : Q} 
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
    rintro rfl,
    split, {
        rintro en_go,
        induction w with head tail hyp generalizing st, {
            use [st, nfa.go.finish],
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
                dsimp [epsnfa_to_nfa],
                use [b, eps_stb, next_bc],
            },
            exact t_term,
        }
    }, {
        rintro ⟨n_t, n_go, n_term⟩,
        dsimp [epsnfa_to_nfa] at n_term,
        induction w with head tail hyp generalizing st, {
            cases n_go,
            use n_term,
        }, {
            rcases n_go with (_ | ⟨_, _, _, _, _, h_nxt, h_go⟩),
            specialize hyp n_go_n h_go,
            simp [epsnfa_to_nfa] at h_nxt,
            rcases h_nxt with ⟨x, x_go, x_nxt⟩,
            exact epsnfa_go_trans x_go (go.step x_nxt hyp),
        }     
    }    
end

theorem epsnfa_to_nfa_eq {L : set (list S)} : epsnfa_lang L → nfa.nfa_lang L :=
begin
    rintro ⟨Q, fQ, dQ, enf, rfl⟩,
    letI := fQ,
    existsi [Q, _, _, epsnfa_to_nfa enf],
    ext x,
    exact epsnfa_to_nfa_accepts_iff_accepts enf x enf.start rfl,    
end

theorem epsnfa_to_dfa_eq {L : set (list S)} : epsnfa_lang L → DFA.dfa_lang L := 
    nfa.nfa_to_dfa_eq ∘ epsnfa_to_nfa_eq

end epsnfa_to_nfa

section nfa_to_epsnfa

open option

variables (n : nfa.NFA S Q) [decidable_pred n.term] 

def nfa_to_epsnfa : epsNFA S (option Q) := {
    start := some n.start,
    term := none,
    next := λ q c, option.cases_on q ∅ (λ q', some '' n.next q' c),
    eps := λ q, option.cases_on q ∅ (λ q', if q' ∈ n.term then {none} else ∅),
}

lemma nfa_to_epsnfa_go_from_finish {en : epsNFA S (option Q)} {w : list S} {fi : option Q}
    : en = nfa_to_epsnfa n → (go en none w fi) → w = [] :=
begin
    rintro rfl (⟨⟩ | ⟨_, _, _, _, _, nxt⟩ | ⟨_, _, _, _, nxt⟩), 
    { refl, },
    { simpa only using nxt },
    { simpa only [nfa_to_epsnfa, mem_empty_eq] using nxt, },
end

lemma nfa_to_epsnfa_accepts_iff_accepts
    {en : epsNFA S (option Q)} (w : list S) (st : Q)
    : en = nfa_to_epsnfa n → (go en (some st) w none ↔ ∃ t : Q, nfa.go n st w t ∧ t ∈ n.term) :=
begin
    rintro rfl,
    split, {
        intro go_enfa,
        generalize hst : some st = ust,
        generalize hfi : (none : option Q) = ufi,
        rw [hst, hfi] at go_enfa,
        induction go_enfa generalizing st, {
            subst hfi,
            injection hst,
        }, {
            substs hst hfi,
            cases go_enfa_n, {
                simpa [nfa_to_epsnfa] using go_enfa_h,
            }, {
                specialize go_enfa_ih rfl go_enfa_n rfl,
                rcases go_enfa_ih with ⟨t, t_go, t_term⟩,
                simp [nfa_to_epsnfa] at go_enfa_h,
                use [t, nfa.go.step go_enfa_h t_go, t_term],
            }
        }, {
            substs hst hfi,
            simp only [forall_prop_of_true] at go_enfa_ih,
            cases go_enfa_n, {
                simp [nfa_to_epsnfa] at go_enfa_h,
                split_ifs at go_enfa_h, {
                    suffices tail_nil : go_enfa_tl = [],
                    subst tail_nil, 
                    use [st, nfa.go.finish, h],
                    refine nfa_to_epsnfa_go_from_finish n rfl _,
                    exact none,
                    assumption,
                }, {
                    simpa [nfa_to_epsnfa, h] using go_enfa_h,
                }
            }, {
                simp [nfa_to_epsnfa] at go_enfa_h,
                split_ifs at go_enfa_h,
                all_goals {simpa only [mem_empty_eq] using go_enfa_h},
            }, 
        }
    }, {
        rintro ⟨t, t_go, t_term⟩, 
        induction t_go, {
            refine go.eps _ go.finish,
            simp only [nfa_to_epsnfa, dite_eq_ite],
            simp only [t_term, if_true, mem_singleton],
        }, {
            refine go.step _ (t_go_ih t_term),
            simpa [nfa_to_epsnfa],
        },
    }
end

theorem nfa_to_epsnfa_eq {L : set (list S)} : nfa.nfa_lang L → epsnfa_lang L :=
begin
    rintro ⟨Q, fQ, dQ, nfa, rfl⟩,
    letI := dQ,
    have tmp : decidable_pred nfa.term := by sorry,
    letI := tmp,
    refine ⟨option Q, _, _, nfa_to_epsnfa nfa, _⟩,
    ext x,
    exact nfa_to_epsnfa_accepts_iff_accepts nfa x nfa.start rfl,
end

theorem dfa_to_epsnfa_eq {L : set (list S)} : DFA.dfa_lang L → epsnfa_lang L := 
    nfa_to_epsnfa_eq ∘ nfa.dfa_to_nfa_eq

end nfa_to_epsnfa

end epsnfa