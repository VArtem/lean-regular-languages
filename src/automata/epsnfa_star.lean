import data.set.basic
import data.set.finite
import automata.epsnfa
import languages.basic
import languages.star

open set epsnfa languages

namespace epsnfa.star

variables {S Q : Type} [fintype S] [fintype Q]

@[derive fintype]
inductive U (Q : Type) [fintype Q] : Type
| start : U
| inside (q : Q) : U

def epsnfa_star (e : epsNFA S Q) : epsNFA S (U Q) := {
    start := U.start,
    term := U.start,
    next := λ q c, begin
        cases q, 
        { exact ∅ },
        { exact U.inside '' (e.next q c) }, 
    end,
    eps := λ q, begin
        cases q, {
            exact {U.inside e.start},
        }, {
            by_cases q = e.term,
            exact U.inside '' e.eps q ∪ {U.start}, 
            exact U.inside '' e.eps q,
        },
    end
}

lemma epsnfa_star_go_inside {e : epsNFA S Q} {a b : Q} {w : list S} 
    :  go e a w b → go (epsnfa_star e) (U.inside a) w (U.inside b) :=
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
        by_cases go_inside_q = e.term;
        simpa [h] using go_inside_h,
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
        refine @go.eps _ _ _ _ _ _ _ (U.inside e.start) _ _ _, {
            simp [epsnfa_star],
        }, {
            convert epsnfa_go_trans (epsnfa_star_go_inside hleft) _,
            rw list.append_nil,
            refine go.eps _ go.finish,
            simp [epsnfa_star],
        }
    }
end

lemma epsnfa_star_list_join {e : epsNFA S Q} {w : list S} {u : U Q}
    : go (epsnfa_star e) u w U.start 
        → ∃ pref l, (pref ++ list.join l = w) ∧ (pref = [] ∧ u = U.start ∨ ∃ (q : Q), u = U.inside q ∧ go e q pref e.term) ∧ (∀ x, x ∈ l → x ∈ lang_of_epsnfa e) :=
begin
    intro go_star,
    generalize hst : (U.start : U Q) = fi,
    rw hst at go_star,
    induction go_star with q  head tail q nxt _ hnxt go_tail ih  _ q nxt _ hnxt go_tail ih, {
        subst hst,
        use [list.nil, list.nil],
        simp,
    }, {
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
    }, {
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
                by_cases q = e.term,
                subst h,
                use [go.finish, hlist], 
                exfalso, simpa [epsnfa_star, h] using hnxt,
            }, {
                convert and.intro (go.eps _ qnxt_go) hlist,
                by_cases q = e.term;
                simpa [epsnfa_star, h] using hnxt,
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

theorem epsnfa_star_correct (e : epsNFA S Q) :
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
    rintro ⟨Q, fQ, enl, langl⟩,
    letI := fQ,
    existsi [U Q, _, epsnfa_star enl],
    rwa [← langl, epsnfa_star_correct],
end

end epsnfa.star