import data.set.basic
import data.set.finite
import data.finset.basic
import automata.epsnfa
import languages.basic

open set epsnfa languages

namespace epsnfa.append

variables {S Q Q1 Q2 : Type} [fintype S] [fintype Q1] [fintype Q2] [decidable_eq Q1] [decidable_eq Q2]

def epsnfa_append (e1 : epsNFA S Q1) (e2 : epsNFA S Q2) : epsNFA S (Q1 ⊕ Q2) := {
    start := sum.inl e1.start,
    term := sum.inr e2.term,
    next := λ q c, sum.cases_on q (λ r, sum.inl '' (e1.next r c)) (λ r, sum.inr '' (e2.next r c)),
    eps := λ q, sum.cases_on q 
        (λ r, if (r = e1.term) 
            then (sum.inl '' (e1.eps r) ∪ {sum.inr e2.start})
            else (sum.inl '' (e1.eps r))) 
        (λ r, sum.inr '' e2.eps r) 
}

lemma epsnfa_append_no_right_left {e1 : epsNFA S Q1} {e2 : epsNFA S Q2} {a : Q2} {b : Q1} {w : list S} 
    : ¬ go (epsnfa_append e1 e2) (sum.inr a) w (sum.inl b) :=
begin
    intro gorl,
    generalize ha : (sum.inr a : sum Q1 Q2) = ua,
    generalize hb : (sum.inl b : sum Q1 Q2) = ub,
    rw [ha, hb] at gorl,
    induction gorl generalizing a, {
        -- base case
        subst hb,
        injection ha,
    },
    all_goals { -- works for both `step` and `eps` cases
        substs ha hb,
        cases gorl_n, {
            simpa [epsnfa_append] using gorl_h,
        }, {
            exact @gorl_ih rfl gorl_n rfl,
        }
    },
end

lemma epsnfa_append_go_left {e1 : epsNFA S Q1} {e2 : epsNFA S Q2} 
    {a b : Q1} {w : list S} 
    :  go e1 a w b ↔ go (epsnfa_append e1 e2) (sum.inl a) w (sum.inl b) :=
begin
    split, {
        intro goleft,
        induction goleft, {
            exact go.finish,
        }, {
            refine go.step _ goleft_ih,
            dsimp [epsnfa_append],
            simpa only [mem_image, exists_eq_right], 
        }, {
            refine go.eps _ goleft_ih,
            dsimp [epsnfa_append],
            by_cases goleft_q = e1.term;
            simpa [h] using goleft_h,
        }
    }, {
        intro goappend,
        generalize ha : (sum.inl a : sum Q1 Q2) = ua,
        generalize hb : (sum.inl b : sum Q1 Q2) = ub,
        rw [ha, hb] at goappend,
        induction goappend generalizing a, {
            subst hb,
            injection ha with ha,
            subst ha,
            exact go.finish,
        }, {
            substs ha hb,
            cases goappend_n, {
                -- contradiction here,
                refine go.step _ (@goappend_ih rfl goappend_n rfl),
                simpa [epsnfa_append] using goappend_h,
            }, {
                exfalso,
                simpa [epsnfa_append] using goappend_h,
            }
        }, 
        case epsnfa.go.eps : _ _ _ _ _ goappend_a {
            substs ha hb,
            cases goappend_n, {
                refine go.eps _ (@goappend_ih rfl goappend_n rfl),
                simp only [epsnfa_append, dite_eq_ite, union_singleton] at goappend_h,
                split_ifs at goappend_h, {
                    subst h,
                    simpa only [mem_image, false_or, mem_insert_iff, exists_eq_right] using goappend_h,
                }, {
                    simpa only [mem_image, exists_eq_right] using goappend_h,
                }
            }, {
                -- need to prove there's no path from right to left
                exfalso,
                exact epsnfa_append_no_right_left goappend_a,
            }
        }
    }
end 

lemma epsnfa_append_go_right {e1 : epsNFA S Q1} {e2 : epsNFA S Q2} 
    {a b : Q2} {w : list S}
    : go e2 a w b ↔ go (epsnfa_append e1 e2) (sum.inr a) w (sum.inr b) :=
begin
    split, {
        intro goright,
        induction goright, {
            exact go.finish,
        }, {
            refine go.step _ goright_ih,
            dsimp [epsnfa_append],
            simpa only [mem_image, exists_eq_right], 
        }, {
            refine go.eps _ goright_ih,
            dsimp [epsnfa_append],
            simpa only [mem_image, exists_eq_right],
        }
    }, {
        intro goappend,
        generalize ha : (sum.inr a : sum Q1 Q2) = ua,
        generalize hb : (sum.inr b : sum Q1 Q2) = ub,
        rw [ha, hb] at goappend,
        induction goappend generalizing a, {
            subst hb,
            injection ha with ha,
            subst ha,
            exact go.finish,
        }, {
            substs ha hb,
            cases goappend_n, {
                -- contradiction here,
                exfalso,
                simpa [epsnfa_append] using goappend_h,
            }, {
                refine go.step _ (@goappend_ih rfl goappend_n rfl),
                simpa [epsnfa_append] using goappend_h,
            }
        }, {
            substs ha hb,
            cases goappend_n, {
                exfalso,
                simpa [epsnfa_append] using goappend_h,
            }, {
                refine go.eps _ (@goappend_ih rfl goappend_n rfl),
                simpa [epsnfa_append] using goappend_h,
            }
        }
    }
end 


lemma epsnfa_append_split {e1 : epsNFA S Q1} {e2 : epsNFA S Q2} {a : Q1} {b : Q2} {w : list S} :
    go (epsnfa_append e1 e2) (sum.inl a) w (sum.inr b) →
    ∃ {left right : list S}, left ++ right = w ∧ go e1 a left e1.term ∧ go e2 e2.start right b :=
begin
    intro goappend,
    generalize ha : (sum.inl a : sum Q1 Q2) = ua,
    generalize hb : (sum.inr b : sum Q1 Q2) = ub,
    rw [ha, hb] at goappend,
    induction goappend generalizing a, {
        subst hb,
        contradiction,
    }, {
        substs ha hb,
        cases goappend_n,
        {
            -- somehow make an induction step
            specialize @goappend_ih rfl goappend_n rfl, 
            rcases goappend_ih with ⟨left, right, rfl, goleft, goright⟩,
            use [goappend_hd :: left, right, list.cons_append _ _ _],
            split, {
                refine go.step _ goleft,
                simpa [epsnfa_append] using goappend_h,
            }, {
                use goright,
            }         
        }, {
            -- contradiction here
            exfalso,
            simpa [epsnfa_append] using goappend_h,
        }
    }, {
        -- both induction base and induction step here
        substs ha hb,
        cases goappend_n, {
            -- next state in left part, only apply induction
            specialize @goappend_ih rfl goappend_n rfl,
            rcases goappend_ih with ⟨left, right, rfl, goleft, goright⟩,
            use [left, right, rfl],
            split, {
                refine go.eps _ goleft,
                simp [epsnfa_append] at goappend_h,
                by_cases a = e1.term;
                simpa [h] using goappend_h,
            }, {
                exact goright,                
            }
        }, {
            -- prev in left, next in right, induction base
            use [[], goappend_tl, rfl],
            simp only [epsnfa_append, dite_eq_ite, union_singleton] at goappend_h,
            split_ifs at goappend_h, {
                -- good case, induction base, no contradiction
                subst h, 
                use go.finish,
                simp only [mem_image, exists_false, mem_insert_iff, or_false, and_false] at goappend_h,
                subst goappend_h,
                apply epsnfa_append_go_right.2,
                assumption,
            }, {
                -- contradiction
                exfalso,
                simpa [h, epsnfa_append] using goappend_h, 
            }
        }
    }
end

theorem epsnfa_append_correct (e1 : epsNFA S Q1) (e2 : epsNFA S Q2):
    lang_of_epsnfa (epsnfa_append e1 e2) = lang_of_epsnfa e1 * lang_of_epsnfa e2 :=
begin
    apply subset.antisymm, {
        intros w goappend,
        rcases epsnfa_append_split goappend with ⟨left, right, rfl, goleft, goright⟩,
        use [left, right, goleft, goright],
    }, {
        rintro _ ⟨left, right, hleft, hright, rfl⟩,
        dsimp at hleft hright,
        apply epsnfa_go_trans (epsnfa_append_go_left.1 hleft),
        refine go.eps _ (epsnfa_append_go_right.1 hright),
        simp only [epsnfa_append, dite_eq_ite, union_singleton],
        simp only [mem_image, if_true, eq_self_iff_true, exists_false, mem_insert_iff, or_false, and_false],
    }
end

theorem append_is_epsnfa {L M : set (list S)}: epsnfa_lang L → epsnfa_lang M → epsnfa_lang (L * M) :=
begin
    rintro ⟨Ql, fQl, dQl, enl, rfl⟩ ⟨Qm, fQm, dQm, enm, rfl⟩,
    resetI,
    refine ⟨_, _, _, epsnfa_append enl enm, epsnfa_append_correct enl enm⟩,
end

end epsnfa.append