import automata.dfa
import regular.regex
import data.list.basic
import regular.list_lemmas

open dfa list

namespace pumping

variables {S : Type} {Q : Type} {L : set (list S)} [fintype S] [fintype Q] [decidable_eq Q]
variables {w : list S}

lemma dfa_word_split (d : DFA S Q) (st : Q) (w : list S):
    (fintype.card Q) ≤ length w →  
    ∃ (x y z : list S) (t : Q), x ++ y ++ z = w ∧ (x ++ y).length ≤ (fintype.card Q) ∧ y ≠ [] ∧ go d st x = t ∧ go d t y = t := 
begin
    rintro hlen,
    have tmp2 : (finset.univ : finset Q).card < (finset.range (fintype.card Q + 1)).card, from by {
        simp only [hlen, finset.card_range],
        rw nat.lt_succ_iff,
        refl,
    },
    have tmp3 := finset.exists_ne_map_eq_of_card_lt_of_maps_to tmp2,
    specialize tmp3 (λ a _, finset.mem_univ (go d st (take a w))),
    rcases tmp3 with ⟨x, hx, y, hy, x_ne_y, go_xy_eq⟩,
    rw finset.mem_range at hx hy,
    replace hx := nat.le_of_lt_succ hx,
    replace hy := nat.le_of_lt_succ hy,
    
    wlog x_lt_y : x ≤ y,
    replace x_lt_y := nat.lt_of_le_and_ne x_lt_y x_ne_y,
    
    use [take x (take y w), drop x (take y w), drop y w, go d st (take x w)],
    simp only [true_and, take_append_drop, eq_self_iff_true], 
    refine ⟨_, _, _, _⟩, {
        rwa [length_take, min_eq_left (le_trans hy hlen)],
    }, {
        exact drop_of_take_of_lt_ne_nil x_lt_y (le_trans hy hlen),
    }, {
        rw [take_take, min_eq_left_of_lt x_lt_y],
    }, {
        rw [← dfa_go_append', go_xy_eq],
        congr,
        exact take_append_drop_of_lt x_lt_y,
    }
end  


lemma dfa_go_repeat {d : DFA S Q} {st : Q} {w: list S} {k : ℕ} :
    go d st w = st → go d st (repeat w k).join = st :=
begin
    intro go_base,
    induction k, {
        simp only [join, go_finish, repeat],
    }, {
        simp only [join, repeat_succ],
        rwa [dfa_go_append', go_base],
    }
end

lemma pumping_lemma :
    dfa_lang L → 
        (∃ (n : ℕ), ∀ w, w ∈ L → n ≤ length w →
        (∃ (x y z : list S), x ++ y ++ z = w ∧ y ≠ [] ∧ (x ++ y).length ≤ n ∧
        ∀ (k : ℕ), x ++ (repeat y k).join ++ z ∈ L)) :=
begin
    rintro ⟨Q, _, _, dfa, rfl⟩,
    resetI,
    use fintype.card Q,
    rintro w w_dfa w_len,
    
    rcases dfa_word_split dfa dfa.start w w_len with ⟨x, y, z, t, xyz, xy_len, ynil, hx, hy⟩,
    
    refine ⟨x, y, z, xyz, ynil, xy_len, λ k, _⟩,     
    simp only [lang_of_dfa, dfa_accepts_word, set.mem_set_of_eq] at w_dfa ⊢,
    rw ← xyz at w_dfa,
    rw [append_assoc, dfa_go_append', hx, dfa_go_append'] at w_dfa ⊢,
    rw dfa_go_repeat hy,
    rwa hy at w_dfa, 
end

lemma pumping_lemma_negation {L : set (list S)} :
    (∀ n : ℕ, ∃ (w : list S), w ∈ L ∧ n ≤ length w ∧
     ∀ (x y z : list S), x ++ y ++ z = w → y ≠ [] → (x ++ y).length ≤ n →
     ∃ k : ℕ, x ++ (repeat y k).join ++ z ∉ L) → ¬dfa_lang L:=
begin
    contrapose,
    push_neg,
    refine pumping_lemma,
end

end pumping