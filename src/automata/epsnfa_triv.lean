import data.set.basic
import data.finset.basic
import automata.epsnfa
import languages.basic
import languages.star

open set epsnfa languages

namespace epsnfa.triv

variables {S : Type} [fintype S]

@[derive fintype, derive decidable_eq]
inductive U : Type
| start : U
| finish : U

def epsnfa_empty : epsNFA S U := {
    start := U.start,
    term := U.finish,
    next := λ q c, ∅, 
    eps := λ q, ∅,
}

theorem epsnfa_empty_eq : lang_of_epsnfa (epsnfa_empty : epsNFA S U) = ∅ :=
begin
    rw eq_empty_iff_forall_not_mem,
    rintro x (_ | _ | _);
    all_goals { simpa [epsnfa_empty] using a_h},
end

theorem empty_is_epsnfa_lang : epsnfa_lang (∅ : set (list S)) := by exactI ⟨U, _, _, epsnfa_empty, epsnfa_empty_eq⟩

def epsnfa_eps : epsNFA S U := {
    start := U.start,
    term := U.finish,
    next := λ q c, ∅, 
    eps := λ q, begin
        cases q,
        exact {U.finish},
        exact ∅,
    end
}

theorem epsnfa_eps_eq : lang_of_epsnfa (epsnfa_eps : epsNFA S U) = {[]} :=
begin
    ext w, split, {
        rintro hw,
        cases hw, {
            exfalso; simpa [epsnfa_eps] using hw_h,
        }, {
            simp [epsnfa_eps] at hw_h,
            subst hw_h,
            cases hw_a,
            simp; 
            exfalso, simpa [epsnfa_eps] using hw_a_h,
            exfalso, simpa [epsnfa_eps] using hw_a_h, 
        }
    }, {
        rintro hw,
        refine go.eps U.finish _ _,
        simp [epsnfa_eps],
        rw [mem_singleton_iff] at hw,
        rw hw,
        exact go.finish,
    }
end

theorem eps_is_epsnfa_lang : epsnfa_lang ({[]} : set (list S)) :=  by exactI ⟨U, _, _, epsnfa_eps, epsnfa_eps_eq⟩

def epsnfa_one (char : S) : epsNFA S U := {
    start := U.start,
    term := U.finish,
    next := λ q c, begin
        cases q,
        by_cases c = char,
        exact {U.finish},
        exact ∅,
        exact ∅,
    end,
    eps := λ q, ∅
}

theorem epsnfa_one_eq {char : S} : lang_of_epsnfa (epsnfa_one char) = {[char]} :=
begin
    ext w, split, {
        rintro hw,
        cases hw, {
            by_cases hw_head = char, {
                simp [epsnfa_one, h] at hw_h,
                substs hw_h h,
                cases hw_a,
                simp,
                exfalso, simpa [epsnfa_one, h] using hw_a_h,
                exfalso, simpa [epsnfa_one, h] using hw_a_h,
            }, {
                exfalso, simpa [epsnfa_one, h] using hw_h,
            }
        }, {
            exfalso; simpa [epsnfa_eps] using hw_h,
        }
    }, {
        rintro hw,
        rw [mem_singleton_iff] at hw,
        rw hw,
        refine go.step _ go.finish,
        simp [epsnfa_one],
    }
end

theorem one_is_epsnfa_lang {char : S} : epsnfa_lang ({[char]} : set (list S)) := 
    by exactI ⟨U, _, _, epsnfa_one char, epsnfa_one_eq⟩

end epsnfa.triv