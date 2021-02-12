import automata.dfa
import regular.regex
import data.list.basic

open dfa list

namespace pumping

variables {S : Type} {Q : Type} {L : set (list S)} [fintype S] [fintype Q] [decidable_eq Q]
variables {w : list S}

lemma dfa_word_split {d : DFA S Q} {st fi : Q}:
    length w = (fintype.card Q) → go d st w = fi →  
    ∃ (x y z : list S) (t : Q), y ≠ [] ∧ go d st x = t ∧ go d t y = t ∧ go d t z = fi := 
begin
    rintro hlen go,
    sorry,
end  


lemma pumping_lemma :
    dfa_lang L → 
        (∃ (n : ℕ), ∀ w, w ∈ L → length w ≥ n →
        (∃ (x y z : list S), x ++ y ++ z = w ∧ y ≠ [] ∧ (x ++ y).length ≤ n ∧
        ∀ (k : ℕ), x ++ (repeat y k).join ++ z ∈ L)) :=
begin
    rintro ⟨Q, _, _, dfa, rfl⟩,
    resetI,
    existsi fintype.card Q,
    rintro w w_dfa w_len,
    have pref := take (fintype.card Q) w,
    sorry,
end

lemma pumping_lemma_negation {L : set (list S)} :
    (∀ n : ℕ, ∃ (w : list S), w ∈ L ∧ length w ≥ n ∧
     ∀ (x y z : list S), x ++ y ++ z = w → y ≠ [] → (x ++ y).length ≤ n →
     ∃ k : ℕ, x ++ (repeat y k).join ++ z ∉ L) → ¬dfa_lang L:=
begin
    contrapose,
    push_neg,
    refine pumping_lemma,
end


theorem non_regular:
    ¬ dfa_lang ({w | ∃ n, w = (repeat bool.ff n) ++ (repeat bool.tt n)}) :=
begin
    apply pumping_lemma_negation,
    intro n,
    use (repeat bool.ff n) ++ (repeat bool.tt n),
    use n,
    simp,
    rintro x y z hxyz ynil hpref,
    use 2,
    rintro l hl,
    sorry,
end


end pumping