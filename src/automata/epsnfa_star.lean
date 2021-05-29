import data.set.basic
import data.set.finite
import automata.epsnfa
import languages.basic
import languages.star

open set epsnfa languages option

namespace epsnfa.star

variables {S Q : Type} [fintype S] [fintype Q] [decidable_eq Q]

def epsnfa_star (e : epsNFA S Q) : epsNFA S (option Q) := {
    start := none,
    term := none,
    next := λ q c, option.rec_on q ∅ (λ q', some '' (e.next q' c)),
    eps := λ q, option.rec_on q {some e.start} (λ r, 
        if (q = e.term) then (some '' e.eps r ∪ {none}) else (some '' e.eps r))
}

lemma epsnfa_star_go_inside {e : epsNFA S Q} {a b : Q} {w : list S} 
    :  go e a w b → go (epsnfa_star e) (some a) w (some b) :=
begin
    intro go_inside,
    induction go_inside, {
        exact go.finish,
    }, {
        refine go.step _ go_inside_ih,
        dsimp [epsnfa_star],
        simpa only [mem_image, exists_eq_right], 
    }, {
        refine go.eps _ go_inside_ih,
        dsimp [epsnfa_star],
        split_ifs,
        { simpa using go_inside_h, },
        { simpa using go_inside_h, },
    }    
end 

lemma epsnfa_star_power {e : epsNFA S Q} {L : set (list S)} (hl : L = lang_of_epsnfa e) {n : ℕ}
    : L^n ⊆ lang_of_epsnfa (epsnfa_star e) :=
begin
    subst hl,
    induction n, {
        simp only [epsnfa_accepts_word, lang_of_epsnfa, mem_set_of_eq, one_def, singleton_subset_iff, pow_zero],
        use go.finish,
    }, {
        rintro w ⟨left, right, hleft, hright, rfl⟩,
        replace hright := n_ih hright,
        refine epsnfa_go_trans _ hright,
        
        convert go.eps _ (epsnfa_go_trans (epsnfa_star_go_inside hleft) (go.eps _ go.finish)), 
        all_goals {
            simp only [list.append_nil, epsnfa_star, set.mem_singleton_iff],
        },
        split_ifs, 
        { simp, }, 
        { simpa using h, },
    }   
end

lemma epsnfa_star_list_join {e : epsNFA S Q} {w : list S} {u : option Q}
    : go (epsnfa_star e) u w none 
        → ∃ pref l, (pref ++ list.join l = w) ∧ 
            (pref = [] ∧ u = none ∨ ∃ (q : Q), u = some q ∧ go e q pref e.term) 
            ∧ (∀ x, x ∈ l → x ∈ lang_of_epsnfa e) :=
begin
    intro go_star,
    generalize hst : (none : option Q) = fi,
    rw hst at go_star,
    induction go_star,
    case epsnfa.go.finish : {
        subst hst,
        use [list.nil, list.nil],
        simp,
    }, 
    case epsnfa.go.step : head tail q nxt f hnxt go_tail ih {
        subst hst,
        specialize ih rfl,
        rcases ih with ⟨pref, l, rfl, hpref, hlist⟩,
        use [head :: pref, l, list.cons_append _ _ _],
        split, {
            right,
            cases q, {
                -- finish, contradiction
                exfalso, simpa [epsnfa_star] using hnxt,
            }, {
                -- inside
                use [q, rfl],
                rcases hpref with ⟨rfl, rfl⟩ | ⟨qnxt, rfl, qnxt_go⟩,
                -- impossible case
                simpa [epsnfa_star] using hnxt,
                simp only [epsnfa_star, mem_image, exists_eq_right] at hnxt,                
                exact go.step hnxt qnxt_go,
            }
        }, {
            exact hlist,
        }
    }, 
    case epsnfa.go.eps : tail q nxt f hnxt go_tail ih {
        subst hst,
        specialize ih rfl,
        rcases ih with ⟨pref, l, rfl, hpref, hlist⟩,
        cases q, {
            -- finish, start new string
            use [list.nil, pref :: l],
            simp,
            rcases hpref with ⟨rfl, rfl⟩ | ⟨qnxt, rfl, qnxt_go⟩,
            simpa [epsnfa_star] using hnxt,
            simp only [epsnfa_star, mem_singleton_iff] at hnxt, 
            rw hnxt at qnxt_go,
            use [qnxt_go, hlist],
        }, {
            -- inside, continue old one
            use [pref, l],
            simp, 
            rcases hpref with ⟨rfl, rfl⟩ | ⟨qnxt, rfl, qnxt_go⟩, {
                simp only [epsnfa_star, union_singleton] at hnxt,
                split_ifs at hnxt, {
                    cases h, cases h, 
                    exact ⟨go.finish, λ x xl, hlist x xl⟩,
                }, {
                    simpa only [mem_image, exists_false, and_false] using hnxt,
                }
            }, {
                refine ⟨go.eps _ _ qnxt_go, hlist⟩,
                simp only [epsnfa_star, dite_eq_ite, union_singleton] at hnxt,
                split_ifs at hnxt;
                simpa only [mem_image, false_or, mem_insert_iff, exists_eq_right] using hnxt,
            }   
        }
    }
end

lemma epsnfa_star_list_join_aux {e : epsNFA S Q} {w : list S} {L : set (list S)} :
    L = lang_of_epsnfa (epsnfa_star e) → w ∈ L → ∃ l (h : ∀ x, x ∈ l → x ∈ lang_of_epsnfa e), w = list.join l :=
begin
    rintro rfl hw,
    replace hw := epsnfa_star_list_join hw,
    rcases hw with ⟨pref, l, rfl, hpref, hlist⟩,
    use l,
    rcases hpref with ⟨rfl, hstart⟩ | ⟨qnxt, hstart, qnxt_go⟩, {
        use [hlist, rfl],
    }, {
        exfalso, simpa [epsnfa_star] using hstart,
    }
end

theorem epsnfa_star_correct {e : epsNFA S Q} :
    lang_of_epsnfa (epsnfa_star e) = kleene_star (lang_of_epsnfa e) :=
begin
    apply subset.antisymm, {
        rintro w hw,
        replace hw := epsnfa_star_list_join_aux rfl hw,
        rwa star_eq_list_join, 
    }, {
        rintro w ⟨n, hw⟩,
        exact epsnfa_star_power rfl hw,
    }
end

theorem star_is_epsnfa {L : set (list S)}: epsnfa_lang L → epsnfa_lang (kleene_star L) :=
begin
    rintro ⟨Q, fQ, dQ, enl, rfl⟩,
    letI := fQ,
    existsi [U Q, _, _, epsnfa_star enl],
    exact epsnfa_star_correct,
end

end epsnfa.star