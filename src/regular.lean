import data.set.basic
import data.set.finite
import data.list.basic

import languages

open set languages

namespace regular

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

@[simp] def lang_of_regex {S : Type} (r : regex S) : set (list S) := { w : list S | regex_accepts_word r w }

def regular_lang {S : Type} (l : set (list S)) := ∃ {r : regex S}, l = lang_of_regex r

@[simp] lemma word_in_lang_iff_exists_parse_tree 
    {S : Type} {L : set (list S)} 
    {r : regex S} {w : list S} (regR : L = lang_of_regex r) : w ∈ L ↔ regex_accepts_word r w := 
begin
    split; finish,
end

theorem union_is_regular {S : Type} {L M : set (list S)} 
    (hl : regular_lang L) (hm : regular_lang M) : regular_lang (L ∪ M) :=
begin
    rcases hl with ⟨ rl, pl ⟩,
    rcases hm with ⟨ rm, pm ⟩,
    use (union rl rm),
    ext,
    split,
    {
        intro xlm,
        cases xlm,
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

theorem concat_is_regular {S : Type} {L M : set (list S)}
    (hl : regular_lang L) (hm : regular_lang M) : regular_lang (append_lang L M) :=
begin
    rcases hl with ⟨ rl, hl ⟩,
    rcases hm with ⟨ rm, hm ⟩,
    use (regex.concat rl rm),
    ext, split,
    {
        rintro ⟨ left, right, hleft, hright, hx ⟩,
        change regex_accepts_word (concat rl rm) x,
        rw hx,
        rw word_in_lang_iff_exists_parse_tree hl at hleft,
        rw word_in_lang_iff_exists_parse_tree hm at hright,
        exact concat_tree hleft hright,
    },
    {
        rintro hx,
        rcases hx with ⟨ left, right, hleft, hright ⟩,
        dsimp [append_lang],
        rw ← word_in_lang_iff_exists_parse_tree hl at hx_a,
        rw ← word_in_lang_iff_exists_parse_tree hm at hx_a_1,
        use [hx_l1, hx_l2, hx_a, hx_a_1],
        refl,
    }
end

theorem star_is_regular {S : Type} {L M : set (list S)}
    (hl : regular_lang L) : regular_lang (kleene_star L) :=
begin
    rcases hl with ⟨ rl, hl ⟩,
    use regex.star rl,
    apply subset.antisymm,
    {
        rintro x ⟨n, hx⟩,
        induction n with n hyp,
        {
            simp only [pow_zero, one_def] at hx,
            rw mem_singleton_iff at hx,
            simp only [mem_set_of_eq, lang_of_regex],
            rw hx,
            exact star_eps_tree, 
        },
        {
            sorry,
        },
    },
    {
        sorry,              
    }
end

end regular