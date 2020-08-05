import data.set.basic
import data.set.finite
import data.list.basic

import languages.basic

open languages

namespace regex

variable {S : Type}

inductive regex (S : Type)
| eps       : regex
| one       : S → regex
| union     : regex → regex → regex
| append    : regex → regex → regex
| star      : regex → regex


inductive regex_accepts_word : regex S → list S → Prop
| eps          : regex_accepts_word regex.eps []
| one          : Π {ch : S}, regex_accepts_word (regex.one ch) [ch]
| append       : Π {l1 l2 : list S} {r1 r2 : regex S}, 
    regex_accepts_word r1 l1 → 
    regex_accepts_word r2 l2 →
    regex_accepts_word (regex.append r1 r2) (l1 ++ l2)
| union_left   : Π {l : list S} {r1 r2 : regex S}, 
    regex_accepts_word r1 l → 
    regex_accepts_word (regex.union r1 r2) l
| union_right  : Π {l1 : list S} {r1 r2 : regex S}, 
    regex_accepts_word r2 l1 → 
    regex_accepts_word (regex.union r1 r2) l1
| star_eps     : Π {r : regex S}, regex_accepts_word (regex.star r) []
| star_concat  : Π {r : regex S} {l1 l2 : list S},
    regex_accepts_word r l1 →
    regex_accepts_word (regex.star r) l2 →
    regex_accepts_word (regex.star r) (l1 ++ l2)


open regex_accepts_word

@[simp] def lang_of_regex (r : regex S) : set (list S) := { w : list S | regex_accepts_word r w }

def regular_lang (l : set (list S)) := ∃ {r : regex S}, l = lang_of_regex r

@[simp] lemma word_in_lang_iff_exists_parse_tree 
    {L : set (list S)} {r : regex S} {w : list S} 
    (regR : L = lang_of_regex r) : w ∈ L ↔ regex_accepts_word r w := 
begin
    split; finish,
end

theorem union_is_regular {L M : set (list S)} 
    (hl : regular_lang L) (hm : regular_lang M) : regular_lang (L ∪ M) :=
begin
    rcases hl with ⟨ rl, pl ⟩,
    rcases hm with ⟨ rm, pm ⟩,
    use regex.union rl rm,
    ext,
    split,
    {
        intro xlm,
        cases xlm,
        rw word_in_lang_iff_exists_parse_tree pl at xlm,
        exact union_left xlm,
        rw word_in_lang_iff_exists_parse_tree pm at xlm,
        exact union_right xlm,
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

theorem concat_is_regular {L M : set (list S)}
    (hl : regular_lang L) (hm : regular_lang M) : regular_lang (append_lang L M) :=
begin
    rcases hl with ⟨ rl, hl ⟩,
    rcases hm with ⟨ rm, hm ⟩,
    use (regex.append rl rm),
    apply set.subset.antisymm,
    {
        rintro _ ⟨ left, right, hleft, hright, rfl ⟩,
        rw word_in_lang_iff_exists_parse_tree hl at hleft,
        rw word_in_lang_iff_exists_parse_tree hm at hright,
        exact append hleft hright, 
    },
    {
        rintro x hx,
        rcases hx with ⟨ left, right, hleft, hright ⟩,
        rw ← word_in_lang_iff_exists_parse_tree hl at hx_a,
        rw ← word_in_lang_iff_exists_parse_tree hm at hx_a_1,
        use [hx_l1, hx_l2, hx_a, hx_a_1, rfl],
    }
end

lemma regex_star_into_list {L : set (list S)} {r : regex S} 
    (hr : L = lang_of_regex r) (w : list S) :
    regex_accepts_word (regex.star r) w ↔ ∃ l (h : ∀ x, x ∈ l → x ∈ L), w = list.join l :=
begin
    split,
    {
        sorry,
    },
    {
        rintro ⟨l, h, rfl⟩,
        induction l with head tail ih,
        {
            use star_eps, 
        },
        {
            apply star_concat,
            rw hr at ih h,
            apply h,
            simp only [list.mem_cons_iff, true_or, eq_self_iff_true],
            apply ih,
            rintro x hx,
            apply h,
            simp only [hx, list.mem_cons_iff, or_true],
        },
    },
end

theorem star_is_regular {L M : set (list S)}
    (hl : regular_lang L) : regular_lang (kleene_star L) :=
begin
    rcases hl with ⟨ rl, hl ⟩,
    use regex.star rl,
    apply set.subset.antisymm,
    {
        suffices hyp : ∀ n, L^n ⊆ lang_of_regex rl.star,
        {
            rintro x ⟨ n, hx ⟩,
            exact hyp n hx,
        },
        intro n,
        induction n with n hyp,
        {
            simp [star_eps], 
        },
        {
            rw pow_succ,
            rintro _ ⟨left, right, hleft, hright, rfl⟩,
            rw word_in_lang_iff_exists_parse_tree hl at hleft,
            exact star_concat hleft (hyp hright),
        },
    },
    {
        rintro x hx,
        rw [star_eq_list_join, ← regex_star_into_list],
        exact hx, 
        exact hl,
        have t : (rl.star = rl.star) := rfl,
        exact t,                        
    }
end

end regex