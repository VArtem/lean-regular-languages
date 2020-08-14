import tactic
import languages.basic
import languages.star
import regular.regex
import automata.dfa

open languages regex dfa

namespace regex.from_dfa

variables {S Q : Type} [fintype S] [fintype Q]

inductive go_restr (dfa : DFA S Q) (allow : finset Q) : Q → list S → Q → Prop
| finish {q : Q}                : go_restr q [] q
| last_step {ch : S} {q : Q}    : go_restr q [ch] (dfa.next q ch)
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
        { refine go.step go.finish },
        { subst go_restr_dfa_a, refine go.step go_restr_dfa_ih },
    }
end

def all_edges (dfa : DFA S Q) (a b : Q) : regex S := sorry

def regex_from_to (dfa : DFA S Q) : Q → Q → finset Q → regex S := sorry
-- | a b finset.empty := dfa_all_edges dfa a b,

theorem dfa_to_regex {L : set (list S)} : dfa_lang L → regex_lang L :=
begin
    rintro ⟨Q, fQ, dfa, rfl⟩,
    sorry,
end

end regex.from_dfa