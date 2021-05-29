import data.list.basic
import tactic

open list

variables {S : Type*} {w : list S}

lemma drop_of_take_of_lt_ne_nil {x y : ℕ} : 
  x < y → y <= w.length → (drop x (take y w)) ≠ nil :=
begin
  rintro xy yw,
  apply ne_nil_of_length_pos,
  rw [length_drop, length_take, min_eq_left yw],
  exact nat.sub_pos_of_lt xy, 
end

lemma take_append_drop_of_lt {x y : ℕ} :
  x < y → take x w ++ drop x (take y w) = take y w :=
begin
  intro xy,
  have hmin : min x y = x, from min_eq_left_of_lt xy,
  nth_rewrite 0 ←hmin,
  rw ← take_take,
  apply take_append_drop,
end

lemma prefix_of_append_of_le_length {a left right: list S} 
  (ha : a.length ≤ left.length) (hpref : a <+: (left ++ right)) : a <+: left :=
begin
  exact prefix_of_prefix_length_le hpref (prefix_append _ _) ha,
end

lemma prefix_of_prefix_append {a left right : list S}
  (ha : a <+: left) : a <+: (left ++ right) :=
begin
  cases ha,
  exact ⟨ha_w ++ right, by rw [←append_assoc, ha_h]⟩,
end

lemma prefix_of_repeat {a : list S} {c : S} {n : ℕ}
  (ha : a <+: repeat c n) : a = repeat c a.length :=
begin
  rw eq_repeat',
  intros b hb,
  cases ha,
  apply eq_of_mem_repeat,
  rw ← ha_h,
  apply mem_append_left _ hb,
end

lemma suffix_of_repeat {a : list S} {c : S} {n : ℕ}
  (ha : a <:+ repeat c n) : a = repeat c a.length :=
begin
  rw eq_repeat',
  intros b hb,
  cases ha,
  apply eq_of_mem_repeat,
  rw ← ha_h,
  apply mem_append_right _ hb,
end

lemma repeat_suffix_of_append_repeat {A : Type*} {n m k : ℕ} {a b : A} : 
  k < n → repeat a n <:+ repeat b m ++ repeat a k → a = b :=
begin
  rintro hnk ⟨beg, happend⟩,
  rw append_eq_append_iff at happend,
  rcases happend with ⟨a', ⟨h1, h2⟩⟩ | ⟨c', ⟨h1, h2⟩⟩, {
    have repeat_a : a' = repeat a a'.length := prefix_of_repeat ⟨repeat a k, h2.symm⟩,
    have repeat_b : a' = repeat b a'.length := suffix_of_repeat ⟨beg, h1.symm⟩,
    apply_fun length at h2,
    have a'_length_pos : 0 < a'.length, from by {
      simp at h2,
      linarith,
    },
    cases a', {
      rw length_pos_iff_ne_nil at a'_length_pos,
      contradiction,
    }, {
      nth_rewrite 0 repeat_a at repeat_b,
      simp only [length, repeat_succ] at repeat_b,
      exact repeat_b.1,
    }
  }, {
    apply_fun length at h2,
    rw [length_append, length_repeat, length_repeat] at h2,
    exfalso,
    linarith,
  },
end


lemma suffix_of_append_eq_append {a b c d : list S} : 
  a.length ≤ c.length → a ++ b = c ++ d → d <:+ b :=
begin
  intros ac ab_cd,
  obtain ⟨a', ⟨h1, h2⟩⟩ | ⟨c', ⟨h1, h2⟩⟩ := append_eq_append_iff.1 ab_cd, {
    apply_fun length at h1,
    simp at h1,
    use [a', h2.symm],
  }, {
    apply_fun length at h1,
    rw [h1, length_append] at ac,
    simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] at ac,
    rw [length_eq_zero] at ac,
    subst ac,
    rw [nil_append] at h2,
    subst h2,
  }
end
