import data.set.basic
import data.set.finite
import logic.relation

namespace dfa
open set

structure DFA (S : Type) (Q : Type) := -- alphabet
    (start : Q) -- starting state
    (term : set Q) -- terminal states
    (next : Q → S → Q) -- transitions


def dfa_goes_to {S Q : Type} (aut : DFA S Q) : Q → list S → Q
| q [] := q
| q (head :: tail) := dfa_goes_to (aut.next q head) tail


lemma same_next_same_goes_to 
    {S Q : Type}
    {d1 d2 : DFA S Q}
    (h : d1.next = d2.next)
    : ∀ (w : list S) (q : Q), dfa_goes_to d1 q w = dfa_goes_to d2 q w := 
begin
    intro w,
    induction w with head tail hyp,
    {
        dsimp [dfa_goes_to],
        tauto!,
    },
    {
        intro q,
        dsimp [dfa_goes_to],
        rw h,
        specialize hyp (d2.next q head),
        assumption,
    },
end


@[simp] def dfa_accepts_word {S Q : Type} (aut : DFA S Q) (w : list S) : Prop := 
    dfa_goes_to aut aut.start w ∈ aut.term

@[simp] def lang_of_dfa {S Q : Type} (aut : DFA S Q) : set (list S) := 
    set_of (dfa_accepts_word aut)

def dfa_lang {S : Type} (lang : set (list S)) : Prop := 
    ∃ {Q : Type} (aut : DFA S Q), lang = lang_of_dfa aut

def compl_dfa {S Q : Type} (aut : DFA S Q) : DFA S Q :=
{
    start := aut.start,
    term := aut.termᶜ,
    next := aut.next,
}

lemma lang_of_compl_dfa_is_compl_of_lang {S Q : Type} (aut : DFA S Q) : 
    lang_of_dfa (compl_dfa aut) = (lang_of_dfa aut)ᶜ :=
begin
    ext w,
    dsimp,
    split,
    {
        intro hw,
        rw @same_next_same_goes_to S Q aut (compl_dfa aut) rfl,
        finish, 
    },
    {
        intro hw,
        rw ← @same_next_same_goes_to S Q aut (compl_dfa aut) rfl,
        finish,
    },
end


theorem compl_is_aut {S : Type} {L : set (list S)} : dfa_lang L → dfa_lang Lᶜ :=
begin
    rintro ⟨ Q, ⟨ aut, h ⟩ ⟩,
    use [Q, compl_dfa aut],
    rw [h, lang_of_compl_dfa_is_compl_of_lang aut],
end


@[simp] lemma word_in_lang_iff_dfa_goes_to_term 
    {S Q : Type} {L : set (list S)} 
    {aut : DFA S Q} {w : list S} (autl : L = lang_of_dfa aut) : w ∈ L ↔ (dfa_goes_to aut aut.start w ∈ aut.term) := 
begin
    split; finish,
end

def inter_dfa {S Ql Qm : Type} (l : DFA S Ql) (m : DFA S Qm) : DFA S (Ql × Qm) :=
{
    start := (l.start, m.start),
    term := { p : (Ql × Qm) | p.1 ∈ l.term ∧ p.2 ∈ m.term },
    next := λ st : Ql × Qm, λ c : S, (l.next st.1 c, m.next st.2 c)
}

lemma inter_dfa_goes_to 
    {S Ql Qm : Type} 
    (l : DFA S Ql) (m : DFA S Qm)
    : ∀ {w : list S} (ql : Ql) (qm : Qm),
        dfa_goes_to (inter_dfa l m) (ql, qm) w = (dfa_goes_to l ql w, dfa_goes_to m qm w) :=
begin
    intro w,
    induction w with head tail hyp,
    {
        simp [inter_dfa, dfa_goes_to],
    },
    {
        intros ql qm,
        specialize hyp (l.next ql head) (m.next qm head),
        finish,
    },
end


theorem inter_is_aut 
    {S : Type} {L M : set (list S)} 
    (hl : dfa_lang L) (hm : dfa_lang M) : dfa_lang (L ∩ M) :=
begin
    rcases hl with ⟨ Ql, ⟨ dl, hl ⟩ ⟩,
    rcases hm with ⟨ Qm, ⟨ dm, hm ⟩ ⟩,
    use [Ql × Qm, inter_dfa dl dm],
    ext,
    split,
    {
        rintro ⟨ xl, xm ⟩,
        rw [lang_of_dfa, mem_set_of_eq],
        have t := @inter_dfa_goes_to S Ql Qm dl dm x dl.start dm.start,
        have tmp : (inter_dfa dl dm).start = (dl.start, dm.start) := rfl,
        rw [dfa_accepts_word, tmp, t],
        rw word_in_lang_iff_dfa_goes_to_term hl at xl,
        rw word_in_lang_iff_dfa_goes_to_term hm at xm,
        split; assumption,        
    },
    {
        intro xInter,
        have t := @inter_dfa_goes_to S Ql Qm dl dm x dl.start dm.start,
        dsimp at xInter,
        have tmp : (inter_dfa dl dm).start = (dl.start, dm.start) := rfl,
        rw [tmp, t] at xInter,
        cases xInter,
        dsimp at xInter_left xInter_right,
        rw ← word_in_lang_iff_dfa_goes_to_term hl at xInter_left,
        rw ← word_in_lang_iff_dfa_goes_to_term hm at xInter_right,
        use [xInter_left, xInter_right], 
    },
end

theorem union_is_aut {S : Type} {L M : set (list S)} 
    (hl : dfa_lang L) (hm : dfa_lang M) : dfa_lang (L ∪ M) :=
begin
    rw union_eq_compl_compl_inter_compl,
    apply compl_is_aut,
    apply inter_is_aut,
    exact compl_is_aut hl,
    exact compl_is_aut hm,
end
    
end dfa