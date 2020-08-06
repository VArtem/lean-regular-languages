import data.list.basic
import tactic.nth_rewrite

variable {S : Type}

open list

lemma is_suffix.antisymm {l1 l2 : list S} : (l1 <:+ l2) → (l2 <:+ l1) → l1 = l2 :=
begin
    intros h1 h2,
    cases h1,
    cases h2,
    rw ← h1_h at h2_h,
    rw ← append_assoc at h2_h,
    suffices tmp : h2_w ++ h1_w = [],
    {
        rw append_eq_nil at tmp,
        replace tmp := tmp.2,
        rwa [tmp, nil_append] at h1_h,
    },
    {
        nth_rewrite 1 ←nil_append l1 at h2_h,
        rwa append_left_inj at h2_h,
    },
end
