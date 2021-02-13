import automata.dfa
import data.list.basic
import regular.regex
import regular.list_lemmas
import regular.pumping_lemma 

open dfa list pumping

def L0ⁿ1ⁿ := {w | ∃ n, w = (repeat bool.ff n) ++ (repeat bool.tt n)}

@[simp] lemma mem_L0ⁿ1ⁿ_iff {w} : w ∈ L0ⁿ1ⁿ ↔ ∃ n, w = (repeat bool.ff n) ++ (repeat bool.tt n) := 
  by simp only [L0ⁿ1ⁿ, set.mem_set_of_eq]

theorem not_regular_0ⁿ1ⁿ : ¬dfa_lang L0ⁿ1ⁿ :=
begin
    apply pumping_lemma_negation,
    intro n,
    use [(repeat bool.ff n) ++ (repeat bool.tt n), n],
    rw length_append,
    simp only [not_exists, true_and, length_repeat, zero_le, le_add_iff_nonneg_left,
  set.mem_set_of_eq],
    rintro x y z hxyz ynil hpref,
    use 0,
    simp only [L0ⁿ1ⁿ, not_exists, join, repeat, set.mem_set_of_eq, append_nil],
    rintro l hl,
    rw ← length_repeat ff n at hpref,
    have tt_n_suffix := suffix_of_append_eq_append hpref hxyz,
    have tt_eq_ff := repeat_suffix_of_append_repeat _ (suffix_trans tt_n_suffix ⟨x, hl⟩),
    contradiction,
    apply_fun length at hxyz hl,
    simp only [length_repeat, append_assoc, length_append] at hxyz hl,
    rw [← length_pos_iff_ne_nil] at ynil,
    linarith,
end

