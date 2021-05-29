import data.set.basic
import data.fintype.basic
import data.finset.basic
import tactic

open set list

variables {S Q : Type} [fintype S] [fintype Q] [decidable_eq Q]

structure DFA (S : Type) (Q : Type) [fintype S] [fintype Q] [decidable_eq Q] :=
    (start : Q) -- starting state
    (term : set Q) -- terminal states
    (next : Q → S → Q) -- transitions

namespace DFA

def go (dfa : DFA S Q) : Q → list S → Q
| q []             := q
| q (head :: tail) := go (dfa.next q head) tail

@[simp] lemma go_finish (dfa : DFA S Q) (q : Q) : go dfa q [] = q := rfl

@[simp] lemma go_step (dfa : DFA S Q) (head : S) (tail : list S) (q : Q) : 
    go dfa q (head :: tail) = go dfa (dfa.next q head) tail := rfl

@[simp] def dfa_accepts_word (dfa : DFA S Q) (w : list S) : Prop := 
    go dfa dfa.start w ∈ dfa.term

@[simp] def lang_of_dfa (dfa : DFA S Q) := {w | dfa_accepts_word dfa w}

def dfa_lang (lang : set (list S)) := 
    ∃ (Q : Type) [fintype Q] [decidable_eq Q], by exactI ∃ {dfa : DFA S Q}, lang = lang_of_dfa dfa 

lemma dfa_go_append {dfa : DFA S Q} {a b c : Q} {left right : list S}:
    go dfa a left = b → go dfa b right = c → go dfa a (left ++ right) = c :=
begin
    induction left with head tail ih generalizing a, {
        rintro ⟨_⟩ hbc,
        exact hbc,
    }, {
        rintro ⟨_⟩ hbc,
        specialize @ih (dfa.next a head) rfl hbc,
        rwa [cons_append, go_step],
    }
end

lemma dfa_go_append' {dfa : DFA S Q} {a : Q} {left right : list S}:
    go dfa a (left ++ right) = go dfa (go dfa a left) right :=
begin
    induction left with head tail ih generalizing a, {
        rw [go_finish, nil_append],
    }, {
        rw [cons_append, go_step, go_step],
        exact @ih (dfa.next a head),
    }
end

lemma dfa_go_append_iff {dfa : DFA S Q} {a c : Q} {left right : list S}:
    (∃ b, go dfa a left = b ∧ go dfa b right = c) ↔ go dfa a (left ++ right) = c :=
begin
    induction left with head tail ih generalizing a, {
        split; simp,
    }, {
        specialize @ih (dfa.next a head),
        refine ih,
    }
end


lemma eq_next_goes_to_iff {q : Q}
    (d1 d2 : DFA S Q) (h : d1.next = d2.next) (w : list S) 
    : go d1 q w = go d2 q w := 
begin
    induction w with head tail ih generalizing q, {
        simp only [go_finish],
    }, {
        specialize @ih (d1.next q head),
        rwa [go_step, go_step, ih, h],
    },
end

@[simp] lemma mem_lang_iff_dfa_accepts 
    {L : set (list S)} {dfa : DFA S Q} {w : list S} (autl : L = lang_of_dfa dfa) 
    : w ∈ L ↔ dfa_accepts_word dfa w := 
begin
    subst autl,
    refl,
end

def compl_dfa (dfa : DFA S Q) : DFA S Q := {
    start := dfa.start,
    term := dfa.termᶜ,
    next := dfa.next,
}

lemma lang_of_compl_dfa_is_compl_of_lang (dfa : DFA S Q) : 
    (lang_of_dfa dfa)ᶜ = lang_of_dfa (compl_dfa dfa) :=
begin
    ext,
    dsimp,
    rw eq_next_goes_to_iff (compl_dfa dfa) dfa rfl,
    simp [compl_dfa],
end

theorem compl_is_dfa {L : set (list S)} : dfa_lang L → dfa_lang Lᶜ :=
begin
    rintro ⟨Q, fQ, dQ, dfa, rfl⟩,
    resetI,
    use [Q, fQ, dQ, compl_dfa dfa],
    exact lang_of_compl_dfa_is_compl_of_lang _,
end

section inter_dfa

variables {Ql Qm : Type} [fintype Ql] [fintype Qm] [decidable_eq Ql] [decidable_eq Qm]

def inter_dfa (l : DFA S Ql) (m : DFA S Qm) : DFA S (Ql × Qm) := {
    start := (l.start, m.start),
    term := l.term.prod m.term,
    next := λ (st : Ql × Qm) (c : S), (l.next st.1 c, m.next st.2 c)
}

@[simp] lemma inter_dfa_start (l : DFA S Ql) (m : DFA S Qm) :
    (inter_dfa l m).start = (l.start, m.start) := rfl

lemma inter_dfa_go (l : DFA S Ql) (m : DFA S Qm) {ql qm}
     : ∀ {w : list S}, go (inter_dfa l m) (ql, qm) w = (go l ql w, go m qm w) :=
begin
    intro w,
    induction w with head tail ih generalizing ql qm, {
        simp only [go_finish],
    }, {
        specialize @ih (l.next ql head) (m.next qm head),
        simpa only,
    },
end

theorem inter_is_dfa {L M : set (list S)} 
    (hl : dfa_lang L) (hm : dfa_lang M) : dfa_lang (L ∩ M) :=
begin
    rcases hl with ⟨Ql, fQl, dQl, dl, rfl⟩,
    rcases hm with ⟨Qm, fQm, dQm, dm, rfl⟩,
    letI := fQl,
    letI := fQm,
    existsi [Ql × Qm, _, _, inter_dfa dl dm],
    ext word, 
    split, {
        rintro ⟨xl, xm⟩,
        dsimp [lang_of_dfa, dfa_accepts_word] at *,
        rw [inter_dfa_go, inter_dfa],
        use [xl, xm],
    }, {
        rintro x_inter,
        dsimp at x_inter,
        rwa [inter_dfa_go, inter_dfa] at x_inter,
    },
end

theorem union_is_dfa {L M : set (list S)} 
    (hl : dfa_lang L) (hm : dfa_lang M) : dfa_lang (L ∪ M) :=
begin
    rw union_eq_compl_compl_inter_compl,
    apply compl_is_dfa,
    apply inter_is_dfa,
    exact compl_is_dfa hl,
    exact compl_is_dfa hm,
end

end inter_dfa
    
end DFA