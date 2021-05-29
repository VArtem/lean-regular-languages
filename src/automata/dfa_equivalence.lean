import data.fintype.basic

structure dfa (S : Type) [fintype S] :=
  (Q : Type) -- states
  [Qfin : fintype Q]
  (start : Q) -- starting state
  (term : set Q) -- terminal states
  (next : Q → S → Q) -- transitions

variables {S : Type} [fintype S] (d : dfa S)

namespace dfa

open_locale classical
noncomputable theory

instance : fintype d.Q := d.Qfin

def go {d : dfa S} : d.Q → list S → d.Q
| q []             := q
| q (head :: tail) := go (d.next q head) tail

@[simp] lemma go_nil (a : d.Q) : go a [] = a := rfl
@[simp] lemma go_cons (a : d.Q) (head : S) (tail : list S) : go a (head :: tail) = go (d.next a head) tail := rfl

@[simp] lemma go_append (q : d.Q) (u v : list S) :
  go q (u ++ v) = go (go q u) v :=
begin
  induction u with hd tl ih generalizing q, {
    simp,
  }, {
    specialize ih (d.next q hd),
    simpa using ih,
  }
end

def state_equiv (d : dfa S) (u v : d.Q) := ∀ (w : list S), go u w ∈ d.term ↔ go v w ∈ d.term

@[simp] lemma state_equiv_def (u v : d.Q) : state_equiv d u v = ∀ w, go u w ∈ d.term ↔ go v w ∈ d.term := rfl

lemma state_equiv_reflexive : reflexive (state_equiv d) := λ v, by simp

lemma state_equiv_symmetric : symmetric (state_equiv d) := λ u v h w, by simp only [h w]

lemma state_equiv_transitive : transitive (state_equiv d) := λ a b c hab hbc w, by simp only [hab w, hbc w]

lemma state_equiv_equivalence: equivalence (state_equiv d) :=
  ⟨state_equiv_reflexive d, state_equiv_symmetric d, state_equiv_transitive d⟩

instance setoid : setoid d.Q := ⟨state_equiv d, state_equiv_equivalence d⟩

def Q' (d : dfa S) := quotient d.setoid

@[simp] lemma state_equiv_equiv (a b : d.Q) : a ≈ b ↔ ∀ w, go a w ∈ d.term ↔ go b w ∈ d.term := by refl

def term' (d : dfa S) : set d.Q' := quotient.lift (d.term)
begin
  rintro a b hab,
  specialize hab [],
  simpa using hab,
end

def next' (d : dfa S) (c : S) : d.Q' → d.Q' := quotient.lift (λ q, ⟦d.next q c⟧)
begin
  rintro a b hab,
  dsimp only,
  rw [quotient.eq, state_equiv_equiv],
  intro w,
  specialize hab (c :: w),
  simpa using hab,
end

def min_dfa (d : dfa S) : dfa S :=
  { Q := Q' d,
    Qfin := quotient.fintype _,
    start := ⟦d.start⟧,
    term  := term' d,
    next  := λ q c, next' d c q}

@[simp] lemma min_dfa_Q {d : dfa S} : (min_dfa d).Q = quotient (d.setoid) := rfl
@[simp] lemma min_dfa_start {d : dfa S} : (min_dfa d).start = ⟦d.start⟧ := rfl
@[simp] lemma min_dfa_term {d : dfa S} {q} : ⟦q⟧ ∈ (min_dfa d).term ↔ q ∈ d.term := by refl
@[simp] lemma min_dfa_next {d : dfa S} {q} {c : S}: (min_dfa d).next ⟦q⟧ c = ⟦d.next q c⟧ := by refl
@[simp] theorem min_dfa_go (d : dfa S) {a} {w}: @go _ _ (min_dfa d) ⟦a⟧ w = ⟦go a w⟧ :=
begin
  induction w with head tail ih generalizing a, {
    simp only [state_equiv_equiv, forall_const, state_equiv_def, iff_self, go_nil],
  }, {
    specialize @ih (d.next a head),
    rw [go, go],
    exact ih,
  },
end

def language (d : dfa S) := {w | go d.start w ∈ d.term}

@[simp] lemma mem_dfa_language_iff {w : list S} {d : dfa S} : 
  w ∈ d.language ↔ go d.start w ∈ d.term := iff.rfl

theorem min_dfa_lang_eq_dfa_lang (d : dfa S) : d.language = (min_dfa d).language :=
begin
  ext,
  simp,
end

theorem min_dfa_card_le (d : dfa S) : fintype.card (min_dfa d).Q ≤ fintype.card d.Q := 
begin
  simp,
  exact fintype.card_quotient_le (dfa.setoid d),
end

def all_reachable (d : dfa S) := ∀ q : d.Q, ∃ w, go d.start w = q

lemma min_dfa_all_reachable {d : dfa S} : d.all_reachable → (min_dfa d).all_reachable :=
begin
  rintro hd q,
  apply quotient.induction_on q, clear q,
  intro q,
  rcases hd q with ⟨w, rfl⟩,
  use w,
  simp,
end

end dfa

namespace right_ctx 

variable {L : set (list S)}

def r (L : set (list S)) (u v : list S) := ∀ w, (u ++ w) ∈ L ↔ (v ++ w) ∈ L

@[simp] lemma r_def {u v} : (r L) u v ↔ ∀ w, (u ++ w) ∈ L ↔ (v ++ w) ∈ L := iff.rfl

def r_refl : reflexive (r L) :=
begin
  intro u,
  simp,
end 

def r_symm : symmetric (r L) := 
begin
  intros u v h w,
  simp [h w],
end

def r_trans : transitive (r L) :=
begin
  intros u v w huv hwv x,
  simp [huv x, hwv x],
end

instance setoid : setoid (list S) := ⟨r L, r_refl, r_symm, r_trans⟩

instance has_equiv : has_equiv (list S) := ⟨r L⟩

#check @right_ctx.setoid

def right_ctx (L : set (list S)) := quotient (@right_ctx.setoid S _ L)

#reduce (setoid.r : list S → list S → Prop)
#reduce (has_equiv.equiv : list S → list S → Prop)

-- @[simp] lemma right_ctx_equiv (u v : list S) :
--   u ≈ v ↔ ∀ w, (u ++ w) ∈ L ↔ (v ++ w) ∈ L := iff.rfl

end right_ctx

namespace myhill_nerode

open dfa right_ctx

def myhill_nerode_equiv {d : dfa S} (hd : d.all_reachable): (min_dfa d).Q ≃ (right_ctx d.language) :=
begin
  letI := @right_ctx.setoid S _ d.language, 
  exact { 
    to_fun := quotient.map (λ q, classical.some (hd q))
    begin
      rintro a b rab,
      simp at rab,
      simp [has_equiv.equiv, setoid.r, r],
      intro w,
      specialize rab w,
      have ha := classical.some_spec (hd a),
      have hb := classical.some_spec (hd b),
      rw [ha, hb],
      exact rab,
    end,
    inv_fun := quotient.lift (λ w, go (min_dfa d).start w)
    begin
      rintro u v ruv,
      simp at ⊢ ruv,
      simpa [has_equiv.equiv, setoid.r] using ruv,
    end,
    left_inv := λ q,  
    begin
      apply quotient.induction_on q, clear q, intro q,
      simp,
      intro w,
      have hq := classical.some_spec (hd q),
      rw hq,      
    end,
    right_inv := λ w,
    begin
      apply quotient.induction_on w, clear w, intro w,
      simp [has_equiv.equiv, setoid.r],
      intro x,
      have hw := classical.some_spec (hd (go d.start w)),
      rw hw,
    end
  },
end

end myhill_nerode