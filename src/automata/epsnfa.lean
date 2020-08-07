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

lemma epsnfa_go_exists_trans {enfa : epsNFA S Q} {a c : Q} 
    {left right concat : list S} {clr : left ++ right = concat}:
    go enfa a concat c → (∃ {b : Q}, go enfa a left b ∧ go enfa b right c) :=
begin
    intros go_ac,
    induction go_ac with q  head tail q n f h prev ih  tail q n f h prev ih generalizing left, {
        rw list.append_eq_nil at clr,
        rcases clr with ⟨rfl, rfl⟩,
        use [q, go.finish, go.finish],
    }, {
        by_cases left_nil : (left = []), {
            subst left_nil,
            dsimp at clr,
            subst clr,
            specialize @ih [],
            use [q, go.finish, go.step h prev],
        }, {
            cases left, contradiction,
            rw [list.cons_append, list.cons.inj_eq] at clr,
            rcases clr with ⟨rfl, rfl⟩,
            rcases @ih left_tl rfl with ⟨b, goleft, goright⟩,
            use [b, go.step h goleft, goright],
        }
    }, {
        subst clr,
        rcases @ih left rfl with ⟨b, goleft, goright⟩,
        use [b, go.eps h goleft, goright],
    }
end

def eps_reach (enfa : epsNFA S Q) (q : Q) (r : Q) := go enfa q [] r

def epsnfa_to_nfa (enfa : epsNFA S Q) : nfa.NFA S Q := {
    start := enfa.start,
    term := {x | ∃ t, eps_reach enfa x t ∧ t ∈ enfa.term},
    next := λ q c, {r | ∃ x y, eps_reach enfa q x ∧ y ∈ enfa.next x c ∧ eps_reach enfa y r}
}

lemma epsnfa_to_nfa_singleton (en : epsNFA S Q) {n : nfa.NFA S Q} (w : S) (s1 e1 : Q)
    : (n = epsnfa_to_nfa en) → (go en s1 [w] e1 ↔ nfa.go n s1 [w] e1) :=
begin
    rintro enfa_nfa,
    split, {
        intro go_enfa,
        induction go_enfa, {
            exact nfa.go.finish,
        }, {
            rcases go_enfa_ih with ⟨_⟩, {
                sorry,
            }, {
                sorry,
            }
        }, {
            sorry,
        }
    }, {
        subst enfa_nfa,
        -- dsimp [epsnfa_to_nfa] at *,
        rintro (_ | ⟨head, tail, q, n, f, h, go_nil⟩),
        rcases go_nil,
        rcases h with ⟨x, y, eps_s1x, ynext, eps_yn⟩,
        exact epsnfa_go_trans eps_s1x (go.step ynext eps_yn),
    }
end

lemma epsnfa_to_nfa_goes_to     
    (en : epsNFA S Q) {n : nfa.NFA S Q} (w : list S) (s1 e1 : Q)
    : (n = epsnfa_to_nfa en) → (w ≠ []) → (go en s1 w e1 ↔ nfa.go n s1 w e1) :=
begin
    rintro enfa_nfa,
    induction w with fst tail hyp generalizing s1, {
        tauto!,
    }, {
        rcases tail with _ | ⟨snd, rest⟩, {
            rintro hdnil,
            clear hdnil hyp,
            refine epsnfa_to_nfa_singleton _ _ _ _ enfa_nfa,
        }, {
            intro h, clear h,
            split, {
                intro go_enfa,
                rcases go_enfa with ⟨_⟩ | ⟨_, _, _, nxt, _, hnxt, prev⟩ | ⟨_, _, nxt, _, hnxt, prev⟩, {
                    specialize @hyp nxt (list.cons_ne_nil _ _),
                    replace hyp := hyp.1 prev,
                    refine @nfa.go.step _ _ _ _ _ _ nxt _ _ hyp,
                    subst enfa_nfa,
                    use [s1, nxt, go.finish, hnxt, go.finish],
                }, {
                    specialize @hyp nxt (list.cons_ne_nil _ _),
                    sorry,
                },
            }, {
                sorry,
            }
        }
    }
end

theorem epsnfa_to_nfa_eq {L : set (list S)} : epsnfa_lang L → nfa.nfa_lang L :=
begin
    rintro ⟨Q, enf, rfl⟩,
    use [Q, epsnfa_to_nfa enf],
    ext x,
    dsimp,
    split, {
        rintro ⟨t, tgo, tterm⟩,
        by_cases (x = []), {
            subst h,
            use enf.start,
            split,
            use [nfa.go.finish],
            use [t, tgo, tterm],
        }, {
            use t,
            have tmp := epsnfa_to_nfa_goes_to enf x (epsnfa_to_nfa enf).start t rfl h,
            rw ← tmp,
            use [tgo, t, epsnfa.go.finish, tterm], 
        }
    }, {
        rintro ⟨t, tgo, tterm⟩,
        by_cases xnil : x = [], {
            subst xnil,
            cases tgo,
            use tterm,
        }, {
            rcases tterm with ⟨endt, endt_epsreach, endt_term⟩,
            use endt,
            have tmp := epsnfa_to_nfa_goes_to enf x (epsnfa_to_nfa enf).start t rfl xnil,
            rw ← tmp at tgo,
            split, {
                convert epsnfa_go_trans tgo endt_epsreach,
                simp only [list.append_nil], 
            }, {
                exact endt_term,
            }
        }
    }
end


end epsnfa