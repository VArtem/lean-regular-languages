import tactic
import languages.basic
import languages.star
import regular.regex
import automata.dfa
import data.set.basic
import data.finset.basic
import data.finset.fold
import data.finset.lattice
import data.fintype.basic
import data.set.finite

open languages regex dfa finset list

namespace regex.from_dfa

variables {S Q : Type} [fintype S] [fintype Q] [decidable_eq S] [decidable_eq Q]

variables (set1 : set Q) (set2 : finset Q)

inductive go_restr (dfa : DFA S Q) (allow : finset Q) : Q → list S → Q → Prop
| finish {q : Q}                    : go_restr q [] q
| last_step {ch : S} {q nxt : Q}    : nxt = dfa.next q ch → go_restr q [ch] nxt
| step {head : S} {tail : list S} {q nxt f : Q} :
    nxt = dfa.next q head → nxt ∈ allow → go_restr nxt tail f → go_restr q (head::tail) f

lemma go_restr_univ (dfa : DFA S Q) {a b : Q} {w : list S}
    : go dfa a w b ↔ go_restr dfa (fintype.elems Q) a w b :=
begin
    split, {
        intro go_dfa,
        induction go_dfa, 
        { exact go_restr.finish }, 
        { refine go_restr.step rfl (finset.mem_univ _) go_dfa_ih, }
    }, {
        intro go_restr_dfa,
        induction go_restr_dfa, 
        { exact go.finish },
        { subst go_restr_dfa_a, refine go.step go.finish },
        { subst go_restr_dfa_a, refine go.step go_restr_dfa_ih },
    }
end

lemma go_restr_subset {dfa : DFA S Q} {a b : Q} {w : list S} {fs1 fs2 : finset Q} :
    fs1 ⊆ fs2 → go_restr dfa fs1 a w b → go_restr dfa fs2 a w b :=
begin
    rintro fsub go_fs1,
    induction go_fs1, 
    { exact go_restr.finish },
    { exact go_restr.last_step go_fs1_a },
    { convert go_restr.step (go_fs1_a) (fsub go_fs1_a_1) go_fs1_ih }
end

lemma go_restr_append {dfa : DFA S Q} {a b c : Q} {left right : list S} {allowed : finset Q} :
    b ∈ allowed → go_restr dfa allowed a left b → go_restr dfa allowed b right c →
    go_restr dfa allowed a (left ++ right) c :=
begin
    rintro b_allowed go_ab go_bc,
    induction go_ab, {
        exact go_restr_subset (subset.refl _) go_bc,
    }, {
        subst go_ab_a,
        exact go_restr.step rfl b_allowed go_bc,
    }, {
        replace go_bc := go_ab_ih b_allowed go_bc,
        refine go_restr.step go_ab_a go_ab_a_1 go_bc,
    }
end

lemma go_restr_list_join {dfa : DFA S Q} {a : Q} {l : list (list S)} {allowed : finset Q} :
    a ∈ allowed → (∀ x, x ∈ l → go_restr dfa allowed a x a) → go_restr dfa allowed a (join l) a :=
begin
    rintro a_allowed hl,
    induction l with head tail lst_ih, {
        simp [go_restr.finish],
    }, {
        refine go_restr_append a_allowed (hl head _) (lst_ih _),
        simp only [mem_cons_iff, true_or, eq_self_iff_true],
        rintro x xtail,
        refine hl x _,
        simp only [xtail, mem_cons_iff, or_true],
    }
end

def all_edges (dfa : DFA S Q) (a b : Q) : set (list S) := 
    (⋃ c : S, if dfa.next a c = b then {[c]} else ∅)

def FW (dfa : DFA S Q) : Q → Q → (list Q) → set (list S)
| a b []                := if a = b then all_edges dfa a b ∪ {[]} else all_edges dfa a b
| a b (head :: tail)    := (FW a b tail) ∪ (FW a head tail * kleene_star (FW head head tail) * FW head b tail)

lemma FW_to_go_restr {dfa : DFA S Q} {a b : Q} {allowed : list Q} {w : list S} :
    w ∈ FW dfa a b allowed → go_restr dfa allowed.to_finset a w b :=
begin
    induction allowed with head tail ih generalizing a b w, {
        intro hw,
        by_cases h : a = b, {
            simp [FW, all_edges, h] at hw,
            rcases hw with hw | ⟨ch, win⟩, {
                substs hw h,
                exact go_restr.finish,
            }, {
                split_ifs at win, {
                    simp only [set.mem_singleton_iff] at win,
                    substs h win,
                    refine go_restr.last_step h_1.symm,
                }, {
                    simpa only [set.mem_empty_eq] using win,
                }
            }
        }, {
            simp [FW, all_edges, h] at hw,
            rcases hw with ⟨i, win⟩,
            split_ifs at win,
            convert go_restr.last_step h_1.symm,  
            simpa only [set.mem_empty_eq] using win,
        }, 
    }, {
        intro hw,
        cases hw, {
            replace hw := ih hw,
            refine go_restr_subset _ hw,
            simp [subset_insert], 
        }, {
            rcases hw with ⟨_, right, ⟨left, mid, hleft, hmid, rfl⟩, hright, rfl⟩,
            replace hleft := ih hleft,
            replace hright := ih hright,
            rw [star_eq_list_join] at hmid,
            rcases hmid with ⟨l, hlist, rfl⟩,
            have h_head : head ∈ (cons head tail).to_finset, by simp only [mem_insert, true_or, eq_self_iff_true, to_finset_cons],
            have h_subset : tail.to_finset ⊆ (cons head tail).to_finset, by simp only [subset_insert, to_finset_cons],
            
            refine go_restr_append h_head _ (go_restr_subset h_subset hright),
            refine go_restr_append h_head (go_restr_subset h_subset hleft) _,
            refine go_restr_list_join h_head _,
            rintro x xtail,
            apply go_restr_subset h_subset (ih (hlist x xtail)),
        }
    }
end

-- inductive go_restr (dfa : DFA S Q) (allow : finset Q) : Q → list S → Q → Prop
-- | finish {q : Q}                    : go_restr q [] q
-- | last_step {ch : S} {q nxt : Q}    : nxt = dfa.next q ch → go_restr q [ch] nxt
-- | step {head : S} {tail : list S} {q nxt f : Q} :
--     nxt = dfa.next q head → nxt ∈ allow → go_restr nxt tail f → go_restr q (head::tail) f


lemma go_restr_split {dfa : DFA S Q} {a b s : Q} {allowed : list Q} {w : list S} : 
    go_restr dfa (s::allowed : list Q).to_finset a w b → 
    (go_restr dfa allowed.to_finset a w b) ∨
    (∃ pref (inf : list (list S)) suf, 
        go_restr dfa allowed.to_finset a pref s ∧ 
        (∀ x, x ∈ inf → go_restr dfa allowed.to_finset s x s) ∧
        go_restr dfa allowed.to_finset s suf b ∧
        pref ++ inf.join ++ suf = w) :=
begin
    intro go_ab,
    induction go_ab with _  _ _ _ nxt_eq  head tail _ nxt _ nxt_eq allow_nxt go_tail ih, {
        left, exact go_restr.finish,
    }, {
        left, exact go_restr.last_step nxt_eq,
    }, {
        by_cases nxt = s, {
            substs h,
            right,
            cases ih, {
                use [[head], [], tail],
                use [go_restr.last_step nxt_eq, forall_mem_nil _, ih],
                simp only [join, eq_self_iff_true, and_self, singleton_append],
            }, {
                rcases ih with ⟨pref, inf, suf, go_pref, go_inf, go_suf, rfl⟩,
                use [[head], pref :: inf, suf],
                use [go_restr.last_step nxt_eq],
                split, {
                    rintro x hx,
                    cases hx, {
                        rw ← hx at go_pref,
                        exact go_pref,
                    }, {
                        exact go_inf x hx,
                    }
                }, {
                    use go_suf,
                    simp only [join, cons_append, eq_self_iff_true, list.append_assoc, and_self, singleton_append],
                }
            }
        }, {
            simp only [h, mem_insert, false_or, to_finset_cons] at allow_nxt,
            cases ih, {
                left,
                refine go_restr.step nxt_eq allow_nxt ih,
            }, {
                right,
                rcases ih with ⟨pref, inf, suf, go_pref, go_inf, go_suf, rfl⟩,
                use [head :: pref, inf, suf],
                use [go_restr.step nxt_eq allow_nxt go_pref],
                use [go_inf, go_suf],
                simp only [cons_append, eq_self_iff_true, and_self],
            }
        }
    }
end  
        

lemma FW_from_go_restr {dfa : DFA S Q} {a b : Q} {allowed : list Q} {w : list S} :
    go_restr dfa allowed.to_finset a w b → w ∈ FW dfa a b allowed :=
begin
    intro go_ab,
    induction allowed with head tail ih generalizing a b w, {
        dsimp [FW, all_edges],
        cases go_ab, {
            simp, 
        }, {
            split_ifs; {
                simp, use [go_ab_ch], simp [go_ab_a.symm],
            },                              
        }, {
            simpa only [to_finset_nil, not_mem_empty] using go_ab_a_1,
        }
    }, {
        dsimp [FW, all_edges],
        replace go_ab := go_restr_split go_ab,
        rcases go_ab with _ | ⟨pref, inf, suf, go_pref, go_inf, go_suf, rfl⟩, {
            left,
            exact ih go_ab, 
        }, {
            right,
            use [pref ++ inf.join, suf, pref, inf.join],
            refine ⟨ih go_pref, _, rfl⟩,
            apply star_eq_list_join.2 ⟨inf, λ x hx, ih (go_inf x hx), rfl⟩,
            use ih go_suf,
        }
    }
end 

lemma FW_is_regex {dfa : DFA S Q} {a b : Q} {allowed : list Q} :
    regex_lang (FW dfa a b allowed) :=
begin
    induction allowed with head tail ih generalizing a b, {
        rw FW,
        split_ifs;
        try {apply union_is_regex _ eps_is_regex}; {
            rw [all_edges, ← set.bUnion_univ],
            lift (set.univ : set S) to finset S using set.finite.of_fintype set.univ,
            apply finset_bUnion_is_regex _,
            exact _inst_3,
            intros c cx,
            by_cases hnext : dfa.next a c = b, {
                simp [hnext],
                exact one_is_regex,
            }, {
                simp [hnext],
                exact empty_is_regex,
            },
            exact _inst_1,
        },
    }, {
        rw FW,
        have rAB := @ih a b,
        have rAH := @ih a head,
        have rHH := @ih head head,
        have rHB := @ih head b,
        apply union_is_regex rAB,
        apply append_is_regex (append_is_regex rAH (star_is_regex rHH)) rHB,
    }
end


lemma FW_is_DFA {dfa : DFA S Q} {allowed : list Q} (hQ : allowed.to_finset = fintype.elems Q) :
    (⋃ c ∈ dfa.term, FW dfa dfa.start c allowed) = lang_of_dfa dfa :=
begin
    apply set.subset.antisymm, {
        apply set.bUnion_subset,
        rintro x x_term w w_fw,
        refine ⟨x, _, x_term⟩,
        rw go_restr_univ,
        rw ← hQ,
        apply FW_to_go_restr w_fw,
    }, {
        rintro w ⟨t, w_go, t_term⟩,
        refine set.mem_bUnion t_term _,
        apply FW_from_go_restr,
        rwa [hQ, ← go_restr_univ],
    }
end

theorem dfa_to_regex {L : set (list S)} : dfa_lang L → regex_lang L :=
begin
    rintro ⟨Q, fQ, dQ, dfa, rfl⟩,
    resetI,
    letI := fQ,
    rcases to_finset_surjective (fintype.elems Q) with ⟨Qlist, hQ⟩,
    rw ← FW_is_DFA hQ,
    lift dfa.term to finset Q using set.finite.of_fintype dfa.term, 
    apply finset_bUnion_is_regex,
    rintro c cx,
    exact FW_is_regex,
end

end regex.from_dfa