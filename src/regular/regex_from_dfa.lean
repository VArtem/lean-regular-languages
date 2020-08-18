import tactic
import languages.basic
import languages.star
import regular.regex
import automata.dfa
import data.finset.basic
import data.finset.fold
import data.finset.lattice
import data.fintype.basic

open languages regex dfa finset

namespace regex.from_dfa

variables {S Q : Type} [fintype S] [fintype Q] [decidable_eq Q]

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
    a ∈ allowed → (∀ x, x ∈ l → go_restr dfa allowed a x a) → go_restr dfa allowed a (list.join l) a :=
begin
    rintro a_allowed hl,
    induction l with head tail lst_ih, {
        simp [go_restr.finish],
    }, {
        refine go_restr_append a_allowed (hl head _) (lst_ih _),
        simp only [list.mem_cons_iff, true_or, eq_self_iff_true],
        rintro x xtail,
        refine hl x _,
        simp only [xtail, list.mem_cons_iff, or_true],
    }
end

def all_edges (dfa : DFA S Q) (a b : Q) : set (list S) := 
    (⋃ c : S, if dfa.next a c = b then {[c]} else ∅)

def FW (dfa : DFA S Q) : Q → Q → (list Q) → set (list S)
| a b []                := if a = b then all_edges dfa a b ∪ {[]} else all_edges dfa a b
| a b (head :: tail)    := (FW a b tail) ∪ (FW a head tail * kleene_star (FW head head tail) * FW head b tail)

lemma FW_nil {dfa : DFA S Q} {a : Q} {allowed : list Q} :
    [] ∈ FW dfa a a allowed :=
begin
    induction allowed, {
        simp only [FW, set.mem_insert_iff, if_true, true_or, eq_self_iff_true, set.union_singleton],
    }, {
        simp only [FW, allowed_ih, true_or, set.mem_union_eq],
    }
end

lemma FW_one {dfa : DFA S Q} {a : Q} {c : S} {allowed : list Q} :
    [c] ∈ FW dfa a (dfa.next a c) allowed :=
begin
    induction allowed, {
        simp [FW, all_edges],
        split_ifs; {
            simp only [set.mem_Union, set.mem_insert_iff, false_or],
            use c, simp,
        }
    }, {
        simp only [FW, allowed_ih, true_or, set.mem_union_eq]
    }
end


lemma FW_subset {dfa : DFA S Q} {a b : Q} {allowed : list Q} :
    (FW dfa a b []) ⊆ (FW dfa a b allowed) :=
begin
    rintro w,
    induction allowed with head tail ih, {
        tauto,
    }, {
        intro lhs,
        specialize ih lhs,
        left, 
        exact ih,
    }
end

lemma FW_split {dfa : DFA S Q} {a b s : Q} {A : list Q} {w : list S} :
    go_restr dfa (insert s A).to_finset a w b → 
        (w ∈ FW dfa a b A) ∨ (∃ pref inf suf, pref ∈ FW dfa a s A ∧ inf ∈ kleene_star (FW dfa s s A) ∧ suf ∈ FW dfa s b A ∧ pref ++ inf ++ suf = w) :=
begin
    intro go,
    induction w with head tail ih generalizing a, {
        cases go, left, 
        apply FW_subset,
        simp [FW],
    }, {
        cases go, {
            left, apply FW_subset, simp [FW, go_a.symm],
            split_ifs; 
            simp [all_edges], use head, simp [go_a],
            use head, simp [go_a],
        }, {
            replace go_a_2 := ih go_a_2,
            rcases go_a_2 with go_no_s | ⟨pref, inf, suf, hpref, hinf, hsuf, rfl⟩, {
                subst go_a,
                by_cases dfa.next a head = s, {
                    subst h,
                    right,
                    use [[head], [], tail],
                    use [FW_one, nil_mem_star, go_no_s],
                    simp only [eq_self_iff_true, and_self, list.singleton_append],
                }, {
                    sorry,       
                }
            }, {
                sorry,
            }
        }
    }
end

lemma FW_correct {dfa : DFA S Q} {a b : Q} {allowed : list Q} {w : list S} :
    w ∈ FW dfa a b allowed ↔ go_restr dfa allowed.to_finset a w b :=
begin
    split, {
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
                have h_head : head ∈ (list.cons head tail).to_finset, by simp only [mem_insert, true_or, eq_self_iff_true, list.to_finset_cons],
                have h_subset : tail.to_finset ⊆ (list.cons head tail).to_finset, by simp only [subset_insert, list.to_finset_cons],
                
                refine go_restr_append h_head _ (go_restr_subset h_subset hright),
                refine go_restr_append h_head (go_restr_subset h_subset hleft) _,
                refine go_restr_list_join h_head _,
                rintro x xtail,
                apply go_restr_subset h_subset (ih (hlist x xtail)),
            }
        }
    }, {
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
                simpa only [list.to_finset_nil, not_mem_empty] using go_ab_a_1,
            }
        }, {
            dsimp [FW, all_edges],
            sorry,
        }
    }
end 


theorem dfa_to_regex {L : set (list S)} : dfa_lang L → regex_lang L :=
begin
    rintro ⟨Q, fQ, dfa, rfl⟩,
    sorry,
end

end regex.from_dfa