import data.set.basic
import data.set.finite
import data.list.basic

namespace regular
open set

inductive regex (S : Type)
| eps       : regex
| one       : S → regex
| union     : regex → regex → regex
| concat    : regex → regex → regex
| star      : regex → regex


inductive regex_accepts_word {S : Type} : regex S → list S → Prop
| eps_tree          : regex_accepts_word regex.eps []
| one_tree          : Π {ch : S}, regex_accepts_word (regex.one ch) [ch]
| concat_tree       : Π {l1 l2 : list S} {r1 r2 : regex S}, 
    regex_accepts_word r1 l1 → 
    regex_accepts_word r2 l2 →
    regex_accepts_word (regex.concat r1 r2) (l1 ++ l2)
| union_left_tree   : Π {l : list S} {r1 r2 : regex S}, 
    regex_accepts_word r1 l → 
    regex_accepts_word (regex.union r1 r2) l
| union_right_tree  : Π {l1 : list S} {r1 r2 : regex S}, 
    regex_accepts_word r2 l1 → 
    regex_accepts_word (regex.union r1 r2) l1
| star_eps_tree     : Π {r : regex S}, regex_accepts_word (regex.star r) []
| star_concat_tree  : Π {r : regex S} {l1 l2 : list S},
    regex_accepts_word r l1 →
    regex_accepts_word (regex.star r) l2 →
    regex_accepts_word (regex.star r) (l1 ++ l2)


open regex
open regex_accepts_word

def lang_of_regex {S : Type} (r : regex S) : set (list S) := { w : list S | regex_accepts_word r w }

def regular_lang {S : Type} (l : set (list S)) := ∃ {r : regex S}, l = lang_of_regex r

@[simp] lemma word_in_lang_iff_exists_parse_tree 
    {S : Type} {L : set (list S)} 
    {r : regex S} {w : list S} (regR : L = lang_of_regex r) : w ∈ L ↔ regex_accepts_word r w := 
begin
    split; finish,
end

theorem union_is_regular {S : Type} {L M : set (list S)} (hl : regular_lang L) (hm : regular_lang M) : regular_lang (L ∪ M) :=
begin
    rcases hl with ⟨ rl, pl ⟩,
    rcases hm with ⟨ rm, pm ⟩,
    unfold regular_lang,
    use union rl rm,
    ext,
    split,
    {
        intro xlm,
        cases xlm;
        dsimp [lang_of_regex],
        rw word_in_lang_iff_exists_parse_tree pl at xlm,
        exact union_left_tree xlm,
        rw word_in_lang_iff_exists_parse_tree pm at xlm,
        exact union_right_tree xlm,
    },
    {
        intro hx,
        cases hx,
        left,
        rwa word_in_lang_iff_exists_parse_tree pl, 
        right,
        rwa word_in_lang_iff_exists_parse_tree pm, 
    },
end

def concat_lang {S : Type} (L M: set (list S)) := { w : list S | ∃ (left : list S) (right : list S), left ∈ L ∧ right ∈ M ∧ w = left ++ right} 

def power_lang {S : Type} (L : set (list S)) : ℕ → set (list S)
| 0             := { [] }
| (nat.succ n)  := concat_lang L (power_lang n)


lemma power_lang_1_eq_lang {S : Type} {L : set (list S)} : L = power_lang L 1 :=
begin
    ext,
    split,
    {
        intro xl,
        dsimp [power_lang, concat_lang],
        use [x, []],
        simp [xl],
    },
    {
        rintro xl, 
        rcases xl with ⟨ lft, rgt, hl, hr, hconcat ⟩,
        rw [power_lang, mem_singleton_iff] at hr, 
        rw hr at hconcat,
        rw list.append_nil at hconcat,
        rw hconcat, assumption,
    }
end

def kleene_star {S : Type} (L : set (list S)) := ⋃₀ {w : set (list S) | ∃ (n : ℕ), w = power_lang L n}

theorem lang_subset_star {S : Type} {L : set (list S)} : L ⊆ kleene_star L :=
begin
    apply subset_sUnion_of_mem,
    use 1,
    exact power_lang_1_eq_lang,
end

end regular