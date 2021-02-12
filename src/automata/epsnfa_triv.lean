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
    rintro x (_ | ⟨_, _, _, _, _, hnxt, _⟩ | ⟨_, _, _, _, hnxt, _⟩);
    simpa [epsnfa_empty] using hnxt,
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
        cases hw, 
        case epsnfa.go.step : {
            exfalso; simpa [epsnfa_eps] using hw_h,
        }, 
        case epsnfa.go.eps : _ _ h_nxt h_go {
            simp [epsnfa_eps] at h_nxt,
            subst h_nxt,
            cases h_go,
            simp only [mem_singleton],
            simpa only [mem_singleton_iff] using h_go_h,
            simpa only [epsnfa_eps, mem_empty_eq] using h_go_h,
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
        cases hw, 
        case epsnfa.go.step : _ _ _ h_nxt h_go { 
            simp only [epsnfa_one, dite_eq_ite] at h_nxt,
            split_ifs at h_nxt, {
                simp [epsnfa_one, h] at h_nxt,
                substs h_nxt h,
                cases h_go,
                simp only [mem_singleton],
                simpa only [mem_singleton_iff, and_false],
                simpa only [epsnfa_one, mem_empty_eq] using h_go_h,
            }, {
                simpa only [mem_empty_eq] using h_nxt,
            }
        }, {
            simpa [epsnfa_one] using hw_h,
        }
    }, {
        rintro hw,
        rw [mem_singleton_iff] at hw,
        subst hw,
        refine go.step _ go.finish,
        simp only [epsnfa_one, dite_eq_ite],
        simp only [if_true, eq_self_iff_true, mem_singleton], 
    }
end


theorem one_is_epsnfa_lang {char : S} : epsnfa_lang ({[char]} : set (list S)) := 
    by exactI ⟨U, _, _, epsnfa_one char, epsnfa_one_eq⟩

end epsnfa.triv