import data.set.basic
import data.set.finite
import data.set.lattice
import data.list.basic
import tactic
import languages.basic
import languages.star
import data.finset.basic
import data.finset.lattice


open languages

namespace regex

variables {S : Type} [fintype S]

inductive regex (S : Type)
| empty     : regex
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

theorem regex_empty_is_empty_lang : lang_of_regex (regex.empty : regex S) = ∅ :=
begin
    rw set.eq_empty_iff_forall_not_mem,
    rintro x ⟨_⟩,
end

theorem empty_is_regex : regex_lang (∅ : set (list S)) := 
begin
    use regex.empty,
    rw regex_empty_is_empty_lang,
end

theorem regex_eps_is_eps_lang : lang_of_regex (regex.eps : regex S) = { [] } :=
begin
    ext x, split, {
        rintro ⟨_⟩,
        simp only [set.mem_singleton], 
    }, {
        intro xnil, 
        convert regex_accepts_word.eps,
        apply_instance,
    }
end

theorem eps_is_regex : regex_lang ({[]} : set (list S)) := 
begin
    use regex.eps,
    rw regex_eps_is_eps_lang,
end


theorem regex_one_is_one_lang {ch : S} : lang_of_regex (regex.one ch) = { [ch] } :=
begin
    ext x, split, {
        rintro ⟨_⟩,
        simp only [set.mem_singleton], 
    }, {
        intro xone, 
        convert regex_accepts_word.one,
        apply_instance,
    }
end

theorem one_is_regex {c : S} : regex_lang ({[c]} : set (list S)) := 
begin
    use regex.one c,
    rw regex_one_is_one_lang,
end

theorem regex_union_is_lang_union {rl rm : regex S}
    : lang_of_regex (regex.union rl rm) = lang_of_regex rl ∪ lang_of_regex rm :=
begin
    apply set.subset.antisymm, {
        rintro x ⟨_⟩,
        left, assumption,
        right, assumption
    }, {
        rintro x (hleft | hright),
        exact regex_accepts_word.union_left hleft, 
        exact regex_accepts_word.union_right hright,
    }, 
end

theorem union_is_regex {L M : set (list S)}: regex_lang L → regex_lang M → regex_lang (L ∪ M) := 
begin
    rintro ⟨rl, rfl⟩ ⟨rm, rfl⟩,
    use regex.union rl rm,
    rw regex_union_is_lang_union,
end

theorem regex_append_is_lang_append {rl rm : regex S}
    : lang_of_regex (regex.append rl rm) = lang_of_regex rl * lang_of_regex rm :=
begin
    apply set.subset.antisymm, {
        rintro x hx,
        rcases hx with _ | _ | ⟨ left, right, _, _, hleft, hright ⟩ | _ | _ | _ | _, -- fun with seven cases
        use [left, right, hleft, hright, rfl], 
    }, {
        rintro _ ⟨ left, right, hleft, hright, rfl ⟩,
        exact regex_accepts_word.append hleft hright,
    }
end

theorem append_is_regex {L M : set (list S)}: regex_lang L → regex_lang M → regex_lang (L * M) := 
begin
    rintro ⟨rl, rfl⟩ ⟨rm, rfl⟩,
    use regex.append rl rm,
    rw regex_append_is_lang_append,
end

lemma regex_star_iff_list_join {L : set (list S)} {r rs: regex S} 
    (hr : L = lang_of_regex rs) (w : list S) (hrs : r = rs.star) :
    regex_accepts_word r w ↔ ∃ l (h : ∀ x, x ∈ l → x ∈ L), w = list.join l :=
begin
    subst hr, 
    split, {
        intro regex_accepts,
        induction regex_accepts with _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ left right rleft rright ih_left ih_right,
        repeat {contradiction}, {
            use list.nil,
            split; simp,
        }, {
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
    }, {
        subst hrs,
        rintro ⟨l, h, rfl⟩,
        induction l with head tail ih, {
            use regex_accepts_word.star_eps, 
        }, {
            apply regex_accepts_word.star_append,
            apply h,
            simp only [list.mem_cons_iff, true_or, eq_self_iff_true],
            apply ih,
            rintro x hx,
            apply h,
            simp only [hx, list.mem_cons_iff, or_true],
        },
    },
end

theorem regex_star_is_kleene_star {rl : regex S}
    : lang_of_regex rl.star = kleene_star (lang_of_regex rl) :=
begin
    apply set.subset.antisymm, {
        rintro x hx,
        rw [star_eq_list_join],
        exact (regex_star_iff_list_join rfl x rfl).1 hx,
    }, {
        suffices hyp : ∀ n, (lang_of_regex rl)^n ⊆ lang_of_regex rl.star, {
            rintro x ⟨ n, hx ⟩,
            exact hyp n hx,
        },
        intro n,
        induction n with n hyp, {
            simp [regex_accepts_word.star_eps], 
        }, {
            rw pow_succ,
            rintro _ ⟨left, right, hleft, hright, rfl⟩,
            exact regex_accepts_word.star_append hleft (hyp hright),
        },
    }
end

theorem star_is_regex {L : set (list S)}: regex_lang L → regex_lang (kleene_star L) := 
begin
    rintro ⟨rl, rfl⟩,
    use regex.star rl,
    rw regex_star_is_kleene_star,
end

theorem finset_bUnion_is_regex {α : Type*} [fintype α] {X : set α} {P : α → set (list S)} [decidable_eq α] : 
    (∀ c ∈ X, regex_lang(P c)) → regex_lang(⋃ c ∈ X, P c) :=
begin
    lift X to finset α using set.finite.of_fintype X,
    rw finset.set_bUnion_coe,
    apply finset.induction_on X, {
        simp only [empty_is_regex, finset.not_mem_empty, set.Union_empty, set.Union_neg, not_false_iff, forall_true_iff],
    }, {
        rintro head tail h_head ih hX,
        rw finset.set_bUnion_insert,
        refine union_is_regex _ _, 
        refine hX _ (finset.mem_insert_self _ _),
        refine ih (λ c c_tail, hX c (finset.mem_insert_of_mem c_tail)),
    },
end

end regex