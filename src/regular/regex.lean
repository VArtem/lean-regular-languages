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
| eps           : regex_accepts_word regex.eps []
| one           : Π {ch : S}, 
                    regex_accepts_word (regex.one ch) [ch]
| append        : Π {l1 l2 : list S} {r1 r2 : regex S}, 
                    regex_accepts_word r1 l1 → regex_accepts_word r2 l2 →
                    regex_accepts_word (regex.append r1 r2) (l1 ++ l2)
| union_left    : Π {l : list S} {r1 r2 : regex S}, 
                    regex_accepts_word r1 l → 
                    regex_accepts_word (regex.union r1 r2) l
| union_right   : Π {l1 : list S} {r1 r2 : regex S}, 
                    regex_accepts_word r2 l1 → 
                    regex_accepts_word (regex.union r1 r2) l1
| star_eps      : Π {r : regex S}, 
                    regex_accepts_word (regex.star r) []
| star_append   : Π {r : regex S} {l1 l2 : list S},
                    regex_accepts_word r l1 → regex_accepts_word (regex.star r) l2 →
                    regex_accepts_word (regex.star r) (l1 ++ l2)

open regex_accepts_word

@[simp] def lang_of_regex (r : regex S) : set (list S) := {w : list S | regex_accepts_word r w}

def regex_lang (l : set (list S)) := ∃ {r : regex S}, l = lang_of_regex r

@[simp] lemma mem_lang_iff_accepts 
    {L : set (list S)} {r : regex S} {w : list S} 
    (regR : L = lang_of_regex r) : w ∈ L ↔ regex_accepts_word r w := 
begin
    split; finish,
end

theorem union_is_regular {L M : set (list S)} 
    (hl : regex_lang L) (hm : regex_lang M) : regex_lang (L ∪ M) :=
begin
    rcases hl with ⟨ rl, pl ⟩,
    rcases hm with ⟨ rm, pm ⟩,
    use regex.union rl rm,
    apply set.subset.antisymm, {
        rintro x ⟨_⟩,
        apply union_left, rwa ←mem_lang_iff_accepts pl,
        apply union_right, rwa ←mem_lang_iff_accepts pm,
    }, {
        rintro x ⟨_⟩,
        left, rwa mem_lang_iff_accepts pl, 
        right, rwa mem_lang_iff_accepts pm, 
    },
end

theorem append_is_regular {L M : set (list S)}
    (hl : regex_lang L) (hm : regex_lang M) : regex_lang (append_lang L M) :=
begin
    rcases hl with ⟨ rl, hl ⟩,
    rcases hm with ⟨ rm, hm ⟩,
    use regex.append rl rm,
    apply set.subset.antisymm, {
        rintro _ ⟨ left, right, hleft, hright, rfl ⟩,
        rw mem_lang_iff_accepts hl at hleft,
        rw mem_lang_iff_accepts hm at hright,
        exact append hleft hright, 
    }, {
        rintro x hx,
        rcases hx with _ | _ | ⟨ left, right, _, _, hleft, hright ⟩ | _ | _ | _ | _, -- fun with seven cases
        rw ← mem_lang_iff_accepts hl at hleft,
        rw ← mem_lang_iff_accepts hm at hright,
        use [left, right, hleft, hright, rfl],
    }
end

lemma regex_star_iff_list_join {L : set (list S)} {r rs: regex S} 
    (hr : L = lang_of_regex rs) (w : list S) (hrs : r = rs.star) :
    regex_accepts_word r w ↔ ∃ l (h : ∀ x, x ∈ l → x ∈ L), w = list.join l :=
begin
    subst hr, 
    split,
    {
        intro regex_accepts,
        induction regex_accepts with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ left right rleft rright ih_left ih_right,
        repeat {contradiction},
        {
            use list.nil,
            split; simp,
        },
        {
            have hrs2 := regex.star.inj hrs,
            subst hrs2,
            clear w ih_left hrs,
            rcases (ih_right rfl) with ⟨ l, h, rfl ⟩,
            use left :: l,
            split, {
                rintro x (xl | xl),
                rwa ← xl at rleft,
                exact h _ xl,
            }, {
                simp only [list.join], 
            }
        }
    },
    {
        subst hrs,
        rintro ⟨l, h, rfl⟩,
        induction l with head tail ih, {
            use star_eps, 
        }, {
            apply star_append,
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
    (hl : regex_lang L) : regex_lang (kleene_star L) :=
begin
    rcases hl with ⟨ rl, hl ⟩,
    use regex.star rl,
    apply set.subset.antisymm, {
        suffices hyp : ∀ n, L^n ⊆ lang_of_regex rl.star, 
        {
            rintro x ⟨ n, hx ⟩,
            exact hyp n hx,
        },
        intro n,
        induction n with n hyp, {
            simp [star_eps], 
        }, {
            rw pow_succ,
            rintro _ ⟨left, right, hleft, hright, rfl⟩,
            rw mem_lang_iff_accepts hl at hleft,
            exact star_append hleft (hyp hright),
        },
    }, {
        rintro x hx,
        rw [star_eq_list_join, ←regex_star_iff_list_join],
        exacts [hx, hl, rfl], 
    }
end

end regex