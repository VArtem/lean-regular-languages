import data.set.basic
import data.set.finite
import automata.epsnfa
import languages.basic

open set epsnfa languages

namespace epsnfa

variables {S Q Q1 Q2 : Type}

inductive U (Q1 Q2 : Type) : Type
| left (q : Q1) : U
| right (q : Q2) : U

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

lemma epsnfa_append_go_left {e1 : epsNFA S Q1} {e2 : epsNFA S Q2} 
    {a b : Q1} {w : list S} 
    :  go e1 a w b ↔ go (epsnfa_append e1 e2) (U.left a) w (U.left b) :=
begin
    split, {
        sorry,
    }, {
        sorry,
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
            refine go.eps _ goright_ih,
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
            sorry,
        }, {
            sorry,
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
        sorry,
    }
end

theorem epsnfa_append_correct (e1 : epsNFA S Q1) (e2 : epsNFA S Q2):
    lang_of_epsnfa e1 * lang_of_epsnfa e2 = lang_of_epsnfa (epsnfa_append e1 e2) :=
begin
    apply subset.antisymm, {
        rintro _ ⟨left, right, hleft, hright, rfl⟩,
        dsimp at hleft hright,
        apply epsnfa_go_trans (epsnfa_append_go_left.1 hleft),
        refine @go.eps _ _ _ _ _ (U.right e2.start) _ _ _,
        simp [epsnfa_append], 
        exact epsnfa_append_go_right.1 hright,
    }, {
        intros w goappend,
        rcases epsnfa_append_split goappend with ⟨left, right, rfl, goleft, goright⟩,
        use [left, right, goleft, goright],
    }
end

end epsnfa