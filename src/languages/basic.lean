import data.set
import logic.function.iterate
import algebra.group_power
import tactic.nth_rewrite
import data.list.basic

open set

namespace languages

variable {S : Type}

@[simp] def append_lang (L M: set (list S)) := 
    { w : list S | ∃ {left right}, left ∈ L ∧ right ∈ M ∧ w = left ++ right} 

-- instance : has_append (set (list S)) := ⟨ append_lang ⟩

@[simp] lemma append_eps (A : set (list S)) : append_lang A {[]} = A :=
begin
    ext, split,
    {
        rintro ⟨ left, right, hleft, hright, rfl ⟩,
        rw mem_singleton_iff at hright,
        rwa [hright, list.append_nil],
    },
    {
        intro xa,
        use [x, []],
        use [xa, mem_singleton [], (list.append_nil x).symm], 
    },
end

@[simp] lemma eps_append (A : set (list S)) : append_lang {[]} A = A :=
begin
    ext, split,
    {
        rintro ⟨ left, right, hleft, hright, rfl ⟩,
        rw mem_singleton_iff at hleft,
        rwa [hleft, list.nil_append], 
    },
    {
        intro xa,
        use [[], x],
        use [xa, (list.nil_append x).symm],
    },
end


lemma append_assoc (A B C : set (list S)) : append_lang (append_lang A B) C = append_lang A (append_lang B C) :=
begin
    ext,
    split,
    {
        rintro ⟨_, right, ⟨ left, mid, hleft, hmid, rfl ⟩, hright, rfl ⟩,
        use [left, mid ++ right, hleft, mid, right, hmid, hright],
        exact list.append_assoc left mid right,
    },
    {
        rintro ⟨left, _, hleft, ⟨ mid, right, hmid, hright, rfl ⟩, rfl ⟩,
        use [left ++ mid, right, left, mid, hleft, hmid, hright],
        exact (list.append_assoc left mid right).symm,
    },
end


instance : monoid (set (list S)) := {
    mul := append_lang,
    mul_assoc := append_assoc,
    one := {[]},
    one_mul := eps_append,
    mul_one := append_eps,
}

@[simp] lemma one_def : (1 : set (list S)) = { [] } := rfl

-- def power (L : set (list S)) : ℕ → set (list S)
-- | 0             := { [] }
-- | (nat.succ n)  := append_lang L (power n)

-- @[simp] def power (L : set (list S)) (n : ℕ): set (list S) := L^n

-- notation L`^{`n`}` := power L n


lemma append_subset_of_subset {A B C D : set (list S)} : A ⊆ C → B ⊆ D → A * B ⊆ C * D :=
begin
    rintro hAC hBD x ⟨ left, right, hleft, hright, rfl ⟩,
    use [left, right, hAC hleft, hBD hright],
end


@[simp] def kleene_star (L : set (list S)) := { w : list S | ∃ (n : ℕ), w ∈ L^n}

@[simp] lemma one_subset_star {L : set (list S)} : 1 ⊆ kleene_star L :=
begin
    rw subset_def,
    intros x hx,
    use 0,
    simpa only [pow_zero],
end


lemma power_subset_star {L : set (list S)} (n : ℕ) : L^n ⊆ kleene_star L :=
begin
    rintro x h, 
    use n,
    exact h,
end

lemma lang_subset_star {L : set (list S)} : L ⊆ kleene_star L :=
begin
    convert power_subset_star 1,
    simp only [pow_one],  
end


lemma power_subset_of_subset {A B : set (list S)} {n : ℕ} : A ⊆ B → A^n ⊆ B^n :=
begin
    intro hAB,
    induction n with n hyp,
    {
        simp only [pow_zero], 
    },
    {
        dsimp [pow_succ],
        apply append_subset_of_subset; 
        assumption,
    },
end

lemma star_subset_of_subset {A B : set (list S)} : A ⊆ B → kleene_star A ⊆ kleene_star B :=
begin
    rintro hAB w ⟨ n, ha ⟩,
    use n,
    exact power_subset_of_subset hAB ha,
end


lemma contain_eps_subset_power {A : set (list S)} {n : ℕ} {heps : 1 ⊆ A} : A ⊆ A^n.succ :=
begin
    induction n with n hyp,
    {
        rw pow_one, 
    },
    {
        rw pow_succ,
        nth_rewrite 0 ←one_mul A,
        apply append_subset_of_subset heps hyp,
    }
end


lemma power_star_eq_star {A : set (list S)} {n : ℕ} : (kleene_star A)^n.succ = kleene_star A :=
begin
    induction n with n hyp,
    {
        simp only [pow_one],
    },
    {
        apply subset.antisymm,
        {
            rw [pow_succ, hyp],
            rintro w ⟨ left, right, ⟨ nleft, hleft ⟩, ⟨ nright, hright ⟩, rfl ⟩,

            use [nleft + nright],
            rw pow_add,
            use [left, right, hleft, hright],
        },
        {
            apply contain_eps_subset_power,
            simp only [one_subset_star],             
        },
    },
end

theorem star_star_eq_star {A : set (list S)} : kleene_star (kleene_star A) = kleene_star A :=
begin
    apply subset.antisymm,
    {
        rintro x ⟨ n, hx ⟩,
        cases n,
        {
            use 0,
            simpa only [pow_zero],
        },
        {
            rw power_star_eq_star at hx,
            exact hx,
        },
    },
    {
        exact star_subset_of_subset lang_subset_star,
    },
end

lemma concat_subset_star {A B L : set (list S)} : 
    A ⊆ kleene_star L → B ⊆ kleene_star L → (A * B) ⊆ kleene_star L :=
begin
    rintro al bl _ ⟨ left, right, hleft, hright, rfl ⟩,
    rcases al hleft with ⟨ an, ah ⟩,
    rcases bl hright with ⟨ bn, bh ⟩,
    use an + bn,
    rw pow_add,
    use [left, right, ah, bh],
end


lemma power_eq_list_join {L : set (list S)} {w : list S} {n : ℕ} : 
    w ∈ L^n ↔ ∃ l (h : ∀ x, x ∈ l → x ∈ L), w = list.join l ∧ l.length = n :=
begin
    split, {
        rintro hw,
        induction n with n hyp generalizing w hw,
        {
            use list.nil,
            simpa [list.forall_mem_nil],
        },
        {
            rw pow_succ at hw,
            rcases hw with ⟨left, right, hleft, hright, rfl⟩,
            rcases hyp hright with ⟨l, h, rfl, rfl⟩,
            use left :: l,
            split,
            {
                rintro x ⟨ _ | _ ⟩,
                exact hleft,
                apply h, exact a, 
            },
            simp only [list.join, list.length, eq_self_iff_true, and_self],
        }
    }, 
    {
        rintro ⟨l, h, rfl, rfl⟩, 
        induction l with head tail hyp,
        {
            simp only [list.join, list.length, one_def, pow_zero, mem_singleton], 
        }, 
        {
            dsimp only [pow_succ, list.join, list.length], 
            use [head, tail.join],
            split,
            {
                apply h head,
                simp only [list.mem_cons_iff, true_or, eq_self_iff_true],
            },
            split,
            {
                apply hyp,
                intros x xtail,
                apply h,
                simp only [list.mem_cons_iff, list.forall_mem_cons'] at *, 
                right, exact xtail,
            },
            refl,
        },
    }
end

lemma star_eq_list_join {L : set (list S)} {w : list S} : 
    w ∈ kleene_star L ↔ ∃ l (h : ∀ x, x ∈ l → x ∈ L), w = list.join l :=
begin
    split,
    {
        rintro ⟨n, hw⟩,
        rcases power_eq_list_join.1 hw with ⟨l, h, ⟨ rfl, rfl ⟩ ⟩,
        use [l, h],
    },
    {
        rintro ⟨l, h, rfl⟩,
        apply power_subset_star (l.length),
        apply power_eq_list_join.2,
        use [l, h],
        simp only [eq_self_iff_true, and_self], 
    }
end

end languages