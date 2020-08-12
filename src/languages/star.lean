import data.set
import logic.function.iterate
import algebra.group_power
import tactic.nth_rewrite
import data.list.basic
import languages.basic

open set

namespace languages

variable {S : Type}

@[simp] def kleene_star (L : set (list S)) := {w : list S | ∃ (n : ℕ), w ∈ L^n}

lemma star_Union (L : set (list S)): kleene_star L = ⋃ (n : ℕ), L^n :=
begin
    apply subset.antisymm, {
        rintro w hw,
        rw mem_Union,
        exact hw,
    }, {
        rintro w hw,
        rw mem_Union at hw,
        exact hw,
    }
end

@[simp] lemma one_subset_star {L : set (list S)} : 1 ⊆ kleene_star L :=
begin    
    intros x hx,
    use 0,
    simpa only [pow_zero],
end

@[simp] lemma power_subset_star {L : set (list S)} (n : ℕ) : L^n ⊆ kleene_star L :=
begin
    rw star_Union,
    refine subset_Union _ _,
end

@[simp] lemma lang_subset_star {L : set (list S)} : L ⊆ kleene_star L :=
begin
    convert power_subset_star 1,
    simp only [pow_one],
end

lemma star_subset_of_subset {A B : set (list S)} : A ⊆ B → kleene_star A ⊆ kleene_star B :=
begin
    rintro hAB w ⟨n, ha⟩,
    use n,
    exact power_subset_of_subset hAB ha,
end

lemma power_star_eq_star {A : set (list S)} (n : ℕ) : (kleene_star A)^n.succ = kleene_star A :=
begin
    induction n with n hyp, {
        simp only [pow_one],
    }, {
        apply subset.antisymm, {
            rw [pow_succ, hyp],
            rintro w ⟨ left, right, ⟨ nleft, hleft ⟩, ⟨ nright, hright ⟩, rfl ⟩,
            use nleft + nright,
            rw pow_add,
            use [left, right, hleft, hright],
        }, {
            apply contain_eps_subset_power,
            simp only [one_subset_star],             
        },
    },
end
                
theorem star_star_eq_star {A : set (list S)} : kleene_star (kleene_star A) = kleene_star A :=
begin
    apply subset.antisymm, {
        rintro x ⟨⟨_⟩, hx⟩, {
            use 0,
            simpa only [pow_zero],
        }, {
            rw power_star_eq_star at hx,
            exact hx,
        },
    }, {
        exact star_subset_of_subset lang_subset_star,
    },
end

lemma append_subset_star {A B L : set (list S)} : 
    A ⊆ kleene_star L → B ⊆ kleene_star L → (A * B) ⊆ kleene_star L :=
begin
    rintro al bl _ ⟨ left, right, hleft, hright, rfl ⟩,
    rcases al hleft with ⟨an, ah⟩,
    rcases bl hright with ⟨bn, bh⟩,
    use an + bn,
    rw pow_add,
    use [left, right, ah, bh],
end

lemma star_eq_list_join {L : set (list S)} {w : list S} : 
    w ∈ kleene_star L ↔ ∃ l (h : ∀ x, x ∈ l → x ∈ L), w = list.join l :=
begin
    split, {
        rintro ⟨n, hw⟩,
        rcases power_eq_list_join.1 hw with ⟨l, h, ⟨rfl, rfl⟩⟩,
        use [l, h],
    }, {
        rintro ⟨l, h, rfl⟩,
        apply power_subset_star (l.length),
        apply power_eq_list_join.2,
        use [l, h],
        simp only [eq_self_iff_true, and_self], 
    }
end

end languages