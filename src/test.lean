inductive bad_eq {Q : Type} : Q → Q → Prop
| finish {q : Q} : bad_eq q q 
| step   {a b : Q} : bad_eq a b → bad_eq a b

lemma bad_eq_eq {Q : Type} {a b : Q} : bad_eq a b → a = b :=
begin
    intro h, induction h, refl, assumption, -- OK
end

inductive U (R : Type) : Type
| wrap : R → U

lemma bad_eq_wrap {Q : Type} {a b : Q} : bad_eq (U.wrap a) (U.wrap b) → a = b :=
begin
    intro h,
    generalize hx : U.wrap a = x,
    generalize hy : U.wrap b = y,
    rw [hx, hy] at h,
    induction h, {
        subst hy,
        injection hx,
    }, {
        subst hx,
        subst hy,
        exact h_ih rfl rfl,
    }
end