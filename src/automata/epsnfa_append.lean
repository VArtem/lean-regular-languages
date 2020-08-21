import data.set.basic
import data.set.finite
import data.finset.basic
import automata.epsnfa
import languages.basic

open set epsnfa languages

namespace epsnfa.append

variables {S Q Q1 Q2 : Type} [fintype S] [fintype Q1] [fintype Q2] [decidable_eq Q1] [decidable_eq Q2]

@[derive fintype, derive decidable_eq]
inductive U (Q1 Q2 : Type) [fintype Q1] [fintype Q2] [decidable_eq Q1] [decidable_eq Q2] : Type
| left : Q1 → U
| right : Q2 → U

def epsnfa_append (e1 : epsNFA S Q1) (e2 : epsNFA S Q2) : epsNFA S (U Q1 Q2) := {
    start := U.left e1.start,
    term := U.right e2.term,
    next := λ q c, begin
        cases q, 
        { exact U.left '' (e1.next q c) },
        { exact U.right '' (e2.next q c) }, 
    end,
    eps := λ q, begin
        cases q, {
            by_cases q = e1.term,
            exact (U.left '' (e1.eps q)) ∪ {U.right e2.start},
            exact (U.left '' (e1.eps q)),
        }, { 
            exact U.right '' e2.eps q,
        },
    end
}

lemma epsnfa_append_no_right_left {e1 : epsNFA S Q1} {e2 : epsNFA S Q2} {a : Q2} {b : Q1} {w : list S} 
    : ¬ go (epsnfa_append e1 e2) (U.right a) w (U.left b) :=
begin
    intro gorl,
    generalize ha : (U.right : Q2 → U Q1 Q2) a = ua,
    generalize hb : (U.left : Q1 → U Q1 Q2) b = ub,
    rw [ha, hb] at gorl,
    induction gorl generalizing a, {
        -- base case
        subst hb,
        contradiction,
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
    :  go e1 a w b ↔ go (epsnfa_append e1 e2) (U.left a) w (U.left b) :=
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
            refine go.eps _ _ goleft_ih,
            dsimp [epsnfa_append],
            by_cases goleft_q = e1.term;
            simpa [h] using goleft_h,
        }
    }, {
        intro goappend,
        generalize ha : (U.left : Q1 → U Q1 Q2) a = ua,
        generalize hb : (U.left : Q1 → U Q1 Q2) b = ub,
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
        }, {
            substs ha hb,
            cases goappend_n, {
                refine go.eps _ _ (@goappend_ih rfl goappend_n rfl),
                by_cases a = e1.term;
                simpa [epsnfa_append, h] using goappend_h,
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
    : go e2 a w b ↔ go (epsnfa_append e1 e2) (U.right a) w (U.right b) :=
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
            refine go.eps _ _ goright_ih,
            dsimp [epsnfa_append],
            simpa only [mem_image, exists_eq_right],
        }
    }, {
        intro goappend,
        generalize ha : (U.right : Q2 → U Q1 Q2) a = ua,
        generalize hb : (U.right : Q2 → U Q1 Q2) b = ub,
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
                refine go.eps _ _ (@goappend_ih rfl goappend_n rfl),
                simpa [epsnfa_append] using goappend_h,
            }
        }
    }
end 


lemma epsnfa_append_split {e1 : epsNFA S Q1} {e2 : epsNFA S Q2} {a : Q1} {b : Q2} {w : list S} :
    go (epsnfa_append e1 e2) (U.left a) w (U.right b) →
    ∃ {left right : list S}, left ++ right = w ∧ go e1 a left e1.term ∧ go e2 e2.start right b :=
begin
    intro goappend,
    generalize ha : (U.left : Q1 → U Q1 Q2) a = ua,
    generalize hb : (U.right : Q2 → U Q1 Q2) b = ub,
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
            use [goappend_head :: left, right, list.cons_append _ _ _],
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
                refine go.eps _ _ goleft,
                simp [epsnfa_append] at goappend_h,
                by_cases a = e1.term;
                simpa [h] using goappend_h,
            }, {
                exact goright,                
            }
        }, {
            -- prev in left, next in right, induction base
            use [[], goappend_tail, rfl],
            by_cases a = e1.term, {
                -- good case, induction base, no contradiction
                subst h, 
                use go.finish,
                simp [epsnfa_append] at goappend_h,
                subst goappend_h,
                exact epsnfa_append_go_right.2 goappend_a,
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
        refine go.eps _ _ (epsnfa_append_go_right.1 hright),
        simp [epsnfa_append],
    }
end

theorem append_is_epsnfa {L M : set (list S)}: epsnfa_lang L → epsnfa_lang M → epsnfa_lang (L * M) :=
begin
    rintro ⟨Ql, fQl, dQl, enl, langl⟩ ⟨Qm, fQm, dQm, enm, langm⟩,
    resetI,
    existsi [U Ql Qm, _, _, epsnfa_append enl enm],   
    substs langl langm,
    exact epsnfa_append_correct enl enm,
end

end epsnfa.append