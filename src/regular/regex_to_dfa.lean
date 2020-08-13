import tactic
import languages.basic
import languages.star
import regular.regex
import automata.dfa
import automata.epsnfa
import automata.epsnfa_append
import automata.epsnfa_star
import automata.epsnfa_triv

open languages regex dfa epsnfa

namespace regex.to_dfa

variable {S : Type}

theorem regex_to_dfa {L : set (list S)} : regex_lang L → dfa_lang L :=
begin
    rintro ⟨r, rfl⟩,
    induction r, { 
        rw regex_empty_is_empty_lang,
        exact epsnfa_to_dfa_eq triv.empty_is_epsnfa_lang,
    }, {
        rw regex_eps_is_eps_lang,
        exact epsnfa_to_dfa_eq triv.eps_is_epsnfa_lang,
    }, {
        rw regex_one_is_single_lang,
        exact epsnfa_to_dfa_eq triv.one_is_epsnfa_lang,
    }, {
        rw regex_union_is_lang_union,
        convert union_is_aut _ _;
        assumption,
    }, {
        rw regex_append_is_lang_append,
        apply epsnfa_to_dfa_eq,
        refine append.append_is_epsnfa (dfa_to_epsnfa_eq _) (dfa_to_epsnfa_eq _ );
        assumption,
    }, {
        rw regex_star_is_kleene_star,
        apply epsnfa_to_dfa_eq,
        refine star.star_is_epsnfa (dfa_to_epsnfa_eq r_ih), 
    }
end

end regex.to_dfa