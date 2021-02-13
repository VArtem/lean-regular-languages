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

variables {S Q : Type} [fintype S] [fintype Q] [decidable_eq S] [decidable_eq Q] {dfa : DFA S Q}

inductive go_restr (dfa : DFA S Q) (allowed : finset Q) : Q → list S → Q → Prop
| finish {q : Q}                    : go_restr q [] q
| last_step {ch : S} {q nxt : Q}    : nxt = dfa.next q ch → go_restr q [ch] nxt
| step {head : S} {tail : list S} {q nxt f : Q} :
    nxt = dfa.next q head → nxt ∈ allowed → go_restr nxt tail f → go_restr q (head::tail) f

lemma go_restr_univ {a b : Q} {w : list S}
    : go_restr dfa (fintype.elems Q) a w b ↔ b = go dfa a w :=
begin
    split, {
        intro go_re,
        induction go_re,
        case go_restr.finish {rw go_finish},
        case go_restr.last_step {simpa}, 
        case go_restr.step : _ _ _ _ _ h_nxt h_allow go_prev {
            rw [go_re_ih, go_step, h_nxt],   
        },
    }, {
        intro go_dfa,
        induction w generalizing a, {
            cases go_dfa, exact go_restr.finish,
        }, {
            cases go_dfa, 
            refine go_restr.step rfl (mem_univ _) (@w_ih (dfa.next a w_hd) rfl), 
        }
    }
end

lemma go_restr_insert {a b ins : Q} {w : list S} {allowlist : list Q} :
    go_restr dfa allowlist.to_finset a w b → go_restr dfa (ins::allowlist).to_finset a w b :=
begin
    rintro go_allowed,
    induction go_allowed, 
    case go_restr.finish : { exact go_restr.finish },
    case go_restr.last_step : _ _ _ h_nxt { exact go_restr.last_step h_nxt, },
    case go_restr.step : _ _ _ _ _ h_nxt h_allow go_prev {
        refine go_restr.step h_nxt _ go_allowed_ih,
        simp only [h_allow, mem_insert, or_true, to_finset_cons],
    }
end

lemma go_restr_append {a b c : Q} {left right : list S} {allowed : finset Q} :
    b ∈ allowed → go_restr dfa allowed a left b → go_restr dfa allowed b right c →
    go_restr dfa allowed a (left ++ right) c :=
begin
    rintro b_allowed go_ab go_bc,
    induction go_ab, 
    case go_restr.finish : { simp only [go_bc, nil_append] }, 
    case go_restr.last_step : _ _ _ h_nxt {
        exact go_restr.step h_nxt b_allowed go_bc,
    },
    case go_restr.step : _ _ _ _ _ h_nxt h_allow go_prev {
        replace go_bc := go_ab_ih b_allowed go_bc,
        refine go_restr.step h_nxt h_allow go_bc, 
    }
end

lemma go_restr_list_join {a : Q} {l : list (list S)} {allowed : finset Q} :
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
            exact go_restr_insert (ih hw),
        }, {
            rcases hw with ⟨_, right, ⟨left, mid, hleft, hmid, rfl⟩, hright, rfl⟩,
            replace hleft := ih hleft,
            replace hright := ih hright,
            rw [star_eq_list_join] at hmid,
            rcases hmid with ⟨l, hlist, rfl⟩,

            have h_head : head ∈ (head::tail).to_finset, by simp only [mem_insert, true_or, eq_self_iff_true, to_finset_cons],
            
            refine go_restr_append h_head _ _,
            refine go_restr_append h_head _ _,
            all_goals {try {apply go_restr_list_join}, try {apply go_restr_insert}, try {assumption}},
            
            rintro x xl,
            specialize ih (hlist x xl),
            exact go_restr_insert ih,
        }
    }
end

-- inductive go_restr (dfa : DFA S Q) (allow : finset Q) : Q → list S → Q → Prop
-- | finish {q : Q}                    : go_restr q [] q
-- | last_step {ch : S} {q nxt : Q}    : nxt = dfa.next q ch → go_restr q [ch] nxt
-- | step {head : S} {tail : list S} {q nxt f : Q} :
--     nxt = dfa.next q head → nxt ∈ allow → go_restr nxt tail f → go_restr q (head::tail) f


lemma go_restr_split {dfa : DFA S Q} {a b s : Q} {allowed : list Q} {w : list S} : 
    go_restr dfa (s :: allowed).to_finset a w b → 
    (go_restr dfa allowed.to_finset a w b) ∨
    (∃ pref (inf : list (list S)) suf, 
        go_restr dfa allowed.to_finset a pref s ∧ 
        (∀ x, x ∈ inf → go_restr dfa allowed.to_finset s x s) ∧
        go_restr dfa allowed.to_finset s suf b ∧
        pref ++ inf.join ++ suf = w) :=
begin
    intro go_ab,
    induction go_ab,
    case finish {
        left, exact go_restr.finish,
    },
    case last_step : ch q nxt h_nxt {
        left, exact go_restr.last_step h_nxt,
    }, 
    case step : head tail q nxt f h_nxt h_allow go_tail ih {
        by_cases nxt = s, {
            subst h,
            right,
            cases ih, {
                use [[head], [], tail],
                use [go_restr.last_step h_nxt, forall_mem_nil _, ih],
                simp only [join, eq_self_iff_true, and_self, singleton_append],
            }, {
                rcases ih with ⟨pref, inf, suf, go_pref, go_inf, go_suf, rfl⟩,
                use [[head], pref :: inf, suf],
                use [go_restr.last_step h_nxt],
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
            simp only [h, mem_insert, false_or, to_finset_cons] at h_allow,
            cases ih, {
                left,
                refine go_restr.step h_nxt h_allow ih,
            }, {
                right,
                rcases ih with ⟨pref, inf, suf, go_pref, go_inf, go_suf, rfl⟩,
                use [head :: pref, inf, suf],
                use [go_restr.step h_nxt h_allow go_pref],
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
        cases go_ab, 
        case go_restr.finish : {
            simp, 
        },
        case go_restr.last_step : _ _ _ go_ab_nxt { 
            split_ifs; {
                simp, use [go_ab_ch], simp [go_ab_nxt], 
            },                              
        }, 
        case go_restr.step : _ _ _ _ _ go_ab_nxt go_ab_allow go_ab_prev {
            simpa only [to_finset_nil, not_mem_empty] using go_ab_allow, 
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

lemma FW_is_regex {dfa : DFA S Q} (a b : Q) {allowed : list Q} :
    regex_lang (FW dfa a b allowed) :=
begin
    induction allowed with head tail ih generalizing a b, {
        rw FW,
        split_ifs;
        try {apply union_is_regex _ eps_is_regex}; {
            rw [all_edges, ← set.bUnion_univ],
            lift (set.univ : set S) to finset S using set.finite.of_fintype set.univ,
            apply finset_bUnion_is_regex,
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
        have rAB := ih a b,
        have rAH := ih a head,
        have rHH := ih head head,
        have rHB := ih head b,
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
        replace w_fw := FW_to_go_restr w_fw,
        rw [hQ, go_restr_univ] at w_fw,
        rw w_fw at x_term,
        exact x_term,
    }, {
        rintro w hw,
        refine set.mem_bUnion hw _,
        apply FW_from_go_restr,
        rw [hQ, go_restr_univ],
    }
end

theorem dfa_to_regex {L : set (list S)} : dfa_lang L → regex_lang L :=
begin
    rintro ⟨Q, fQ, dQ, dfa, rfl⟩,
    resetI,
    letI := fQ,
    rcases to_finset_surjective (fintype.elems Q) with ⟨Qlist, hQ⟩,
    rw ← FW_is_DFA hQ,

    apply finset_bUnion_is_regex,
    rintro c cx,
    exact FW_is_regex dfa.start c,
end

end regex.from_dfa