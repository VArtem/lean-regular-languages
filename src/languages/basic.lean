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

@[simp] lemma append_eps (A : set (list S)) : append_lang A {[]} = A :=
begin
    apply subset.antisymm, {
        rintro _ ⟨left, right, hleft, hright, rfl⟩,
        rw mem_singleton_iff at hright,
        rwa [hright, list.append_nil],
    }, {
        rintro x xa,
        use [x, [], xa, mem_singleton [], (list.append_nil x).symm], 
    },
end

@[simp] lemma eps_append (A : set (list S)) : append_lang {[]} A = A :=
begin
    apply subset.antisymm, {
        rintro _ ⟨ left, right, hleft, hright, rfl ⟩,
        rw mem_singleton_iff at hleft,
        rwa [hleft, list.nil_append], 
    }, {
        rintro x xa,
        use [[], x, xa, (list.nil_append x).symm],
    },
end

lemma append_assoc (A B C : set (list S)): 
    append_lang (append_lang A B) C = append_lang A (append_lang B C) :=
begin
    apply subset.antisymm, {
        rintro _ ⟨_, right, ⟨ left, mid, hleft, hmid, rfl ⟩, hright, rfl ⟩,
        use [left, mid ++ right, hleft, mid, right, hmid, hright],
        exact list.append_assoc left mid right,
    }, {
        rintro _ ⟨left, _, hleft, ⟨ mid, right, hmid, hright, rfl ⟩, rfl ⟩,
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

@[simp] lemma one_def : (1 : set (list S)) = {list.nil} := rfl

lemma append_subset_of_subset {A B C D : set (list S)} : A ⊆ C → B ⊆ D → A * B ⊆ C * D :=
begin
    rintro hAC hBD x ⟨left, right, hleft, hright, rfl⟩,
    use [left, right, hAC hleft, hBD hright],
end

lemma power_subset_of_subset {A B : set (list S)} {n : ℕ} : A ⊆ B → A^n ⊆ B^n :=
begin
    intro hAB,
    induction n with n hyp, {
        simp only [pow_zero],
    }, {
        rw pow_succ,
        apply append_subset_of_subset; 
        assumption,
    },
end

lemma contain_eps_subset_power {A : set (list S)} {n : ℕ} {heps : 1 ⊆ A} : A ⊆ A^n.succ :=
begin
    induction n with n hyp, {
        rw pow_one, 
    }, {
        rw pow_succ,
        nth_rewrite 0 ←one_mul A,
        apply append_subset_of_subset heps hyp,
    }
end

lemma power_eq_list_join {L : set (list S)} {w : list S} {n : ℕ} : 
    w ∈ L^n ↔ ∃ l (h : ∀ x, x ∈ l → x ∈ L), w = list.join l ∧ l.length = n :=
begin
    split, {
        rintro hw,
        induction n with n hyp generalizing w hw, {
            use list.nil,
            simp only [mem_singleton_iff, one_def, pow_zero] at hw,
            simp only [hw, list.not_mem_nil, list.join, forall_const, forall_prop_of_false, list.length, eq_self_iff_true, not_false_iff,
  and_self],
        }, {
            rw pow_succ at hw,
            rcases hw with ⟨left, right, hleft, hright, rfl⟩,
            rcases hyp hright with ⟨l, h, rfl, rfl⟩,
            use [left :: l],
            simpa only [hleft, true_and, list.join, forall_eq_or_imp, and_true, list.mem_cons_iff, list.length, eq_self_iff_true],
        }
    }, {
        rintro ⟨l, h, rfl, rfl⟩, 
        induction l with head tail hyp, {
            simp only [list.join, list.length, one_def, pow_zero, mem_singleton], 
        }, {
            use [head, tail.join],
            split, {
                apply h head,
                apply list.mem_cons_self,
            },
            split, {
                apply hyp,
                intros x hx,
                refine (h _ _),
                simp only [hx, list.mem_cons_iff, or_true],
            },
            refl,
        },
    }
end

end languages