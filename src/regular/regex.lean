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

inductive regex.accepts : regex S → list S → Prop
| eps : 
    regex.accepts regex.eps []
| one {ch : S} : 
    regex.accepts (regex.one ch) [ch]
| append {l1 l2 r1 r2} :
    regex.accepts r1 l1 → 
    regex.accepts r2 l2 →
    regex.accepts (regex.append r1 r2) (l1 ++ l2)
| union_left {l r1 r2} :  
    regex.accepts r1 l → 
    regex.accepts (regex.union r1 r2) l
| union_right {l r1 r2} :
    regex.accepts r2 l →
    regex.accepts (regex.union r1 r2) l
| star_eps {r} :
    regex.accepts (regex.star r) []
| star_append {r l1 l2} : 
    regex.accepts r l1 → 
    regex.accepts (regex.star r) l2 →
    regex.accepts (regex.star r) (l1 ++ l2)


def regex_lang (l : set (list S)) := ∃ r : regex S, r.accepts = l 

lemma regex_empty_not_accepts {w : list S} : ¬ regex.empty.accepts w := λ h, by cases h

theorem regex_empty_is_empty_lang : regex.empty.accepts = (∅ : set (list S)) :=
    by {ext, split; rintro ⟨⟩}

theorem empty_is_regex : regex_lang (∅ : set (list S)) := 
    ⟨regex.empty, regex_empty_is_empty_lang⟩

theorem regex_eps_is_eps_lang : regex.eps.accepts = ({[]} : set (list S)) :=
begin
    ext x, split, {
        rintro ⟨_⟩,
        simp only [set.mem_singleton], 
    }, {
        intro xnil,
        convert regex.accepts.eps,
    }
end

theorem eps_is_regex : regex_lang ({[]} : set (list S)) := 
    ⟨regex.eps, regex_eps_is_eps_lang⟩

theorem regex_one_is_one_lang {ch : S} : (regex.one ch).accepts = ({[ch]} : set (list S)) :=
begin
    ext x, split, {
        rintro ⟨_⟩,
        simp only [set.mem_singleton], 
    }, {
        intro xone, 
        convert regex.accepts.one,
    }
end

theorem one_is_regex {c : S} : regex_lang ({[c]} : set (list S)) := 
    ⟨regex.one c, regex_one_is_one_lang⟩

theorem regex_union_is_lang_union {rl rm : regex S}
    : (regex.union rl rm).accepts = (rl.accepts ∪ rm.accepts : set (list S)) :=
begin
    apply set.subset.antisymm, 
    { rintro x (_ | _),
      left, assumption,
      right, assumption },
    { rintro x (hleft | hright),
      exact regex.accepts.union_left hleft, 
      exact regex.accepts.union_right hright,
    },
end

theorem union_is_regex {L M : set (list S)}: regex_lang L → regex_lang M → regex_lang (L ∪ M) := 
begin
    rintro ⟨rl, rfl⟩ ⟨rm, rfl⟩,
    use regex.union rl rm,
    rw regex_union_is_lang_union,
end

theorem regex_append_is_lang_append {rl rm : regex S} :
    (rl.append rm).accepts = (rl.accepts * rm.accepts : set (list S)) :=
begin
    apply set.subset.antisymm, {
        rintro x h,
        rcases h with (_ | _ | ⟨left, right, _, _, hleft, hright⟩ | _ | _ | _ | _),
        use [left, right, hleft, hright, rfl], 
    }, {
        rintro _ ⟨ left, right, hleft, hright, rfl ⟩,
        exact regex.accepts.append hleft hright,
    }
end

theorem append_is_regex {L M : set (list S)}: regex_lang L → regex_lang M → regex_lang (L * M) := 
begin
    rintro ⟨rl, rfl⟩ ⟨rm, rfl⟩,
    exact ⟨regex.append rl rm, regex_append_is_lang_append⟩,
end

lemma regex_star_iff_list_join {r rs : regex S} 
    (hrs : rs = r.star) (w : list S)  :
    rs.accepts w ↔ ∃ l (h : ∀ x, x ∈ l → r.accepts x), w = list.join l :=
begin
    split, {
        intro rsw,
        induction rsw,
        repeat {contradiction},
        case star_eps : {
            use list.nil,
            simp,
        },
        case star_append : _ left right rleft rright ih_left ih_right {
            rcases hrs with ⟨_⟩,
            rcases ih_right hrs with ⟨l, h, rfl⟩,
            refine ⟨left :: l, _, rfl⟩,
            rw list.ball_cons,
            exact ⟨rleft, h⟩,
        },
    }, {
        subst hrs,
        rintro ⟨l, h, rfl⟩,
        induction l with head tail ih, {
            use regex.accepts.star_eps, 
        }, {
            rw list.ball_cons at h,
            refine regex.accepts.star_append (h.1) (ih h.2),
        },
    },
end

theorem regex_star_is_kleene_star {rl : regex S}
    : rl.star.accepts = kleene_star (rl.accepts) :=
begin
    ext w,
    rw star_eq_list_join,
    exact regex_star_iff_list_join rfl w,
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