import data.set.basic
import data.set.finite
import data.finset
import tactic

import automata.lemmas

namespace dfa
open set relation list

variables {S Q : Type}
-- variables fS fQ : fintype S 

structure DFA (S : Type) (Q : Type) := -- alphabet
    (start : Q) -- starting state
    (term : set Q) -- terminal states
    (next : Q → S → Q) -- transitions
    

inductive go (dfa : DFA S Q) : Q → list S → Q → Prop
| finish : Π {q : Q}, go q [] q
| step   : Π {head : S} {tail : list S} {q f : Q},
    go (dfa.next q head) tail f → go q (head::tail) f 

@[simp] lemma dfa_go_step_iff (dfa : DFA S Q) (q : Q) {head : S} {tail : list S} :
    go dfa q (head :: tail) = go dfa (dfa.next q head) tail :=
begin
    ext, split,
    { rintro ⟨ _ ⟩, assumption },
    { exact go.step }, 
end

lemma dfa_go_exists_unique (dfa : DFA S Q) (a : Q) (l : list S):
    ∃! {b : Q}, go dfa a l b :=
begin
    induction l with head tail hyp generalizing a,
    {
        use [a, go.finish],
        intros y h,
        cases h,
        refl,
    },  
    {
        specialize @hyp (dfa.next a head),
        convert hyp,
        dsimp,
        rwa dfa_go_step_iff,        
    }
end

lemma dfa_go_unique {dfa : DFA S Q} {a b c : Q} {l : list S}:
    go dfa a l b → go dfa a l c → b = c :=
begin
    rcases dfa_go_exists_unique dfa a l with ⟨d, dgo, h⟩,
    dsimp at *,
    intros bgo cgo,
    replace bgo := h b bgo,
    replace cgo := h c cgo,
    finish,     
end


lemma eq_next_goes_to 
    {S Q : Type}
    {d1 d2 : DFA S Q}
    (h : d1.next = d2.next)
    {w : list S} {q r : Q}
    : go d1 q w r ↔ go d2 q w r := 
begin
    induction w with head tail hyp generalizing q,
    {
        split;
        { intro h, cases h, exact go.finish }
    },
    {
        specialize @hyp (d1.next q head),
        rw dfa_go_step_iff d1 at *,
        rw dfa_go_step_iff d2 at *,
        rwa h at *,
    },
end


@[simp] def dfa_accepts_word (dfa : DFA S Q) (w : list S) : Prop := 
    ∃ {t}, go dfa dfa.start w t ∧ t ∈ dfa.term

@[simp] def lang_of_dfa (dfa : DFA S Q) : set (list S) := 
    set_of (dfa_accepts_word dfa)

def dfa_lang (lang : set (list S)) : Prop := 
    ∃ {Q : Type} (dfa : DFA S Q), lang = lang_of_dfa dfa

@[simp] lemma mem_lang_iff_dfa_acc 
    {S Q : Type} {L : set (list S)} 
    {dfa : DFA S Q} {w : list S} (autl : L = lang_of_dfa dfa) : w ∈ L ↔ (dfa_accepts_word dfa w) := 
begin
    split; finish,
end

def compl_dfa (dfa : DFA S Q) : DFA S Q :=
{
    start := dfa.start,
    term := dfa.termᶜ,
    next := dfa.next,
}

lemma lang_of_compl_dfa_is_compl_of_lang (dfa : DFA S Q) : 
    lang_of_dfa (compl_dfa dfa) = (lang_of_dfa dfa)ᶜ :=
begin
    apply subset.antisymm,
    {
        rw subset_compl_iff_disjoint,
        rw eq_empty_iff_forall_not_mem,
        rintro x ⟨⟨t, tgo, tterm⟩, ⟨r, rgo, rterm⟩⟩,
        rw @eq_next_goes_to S Q (compl_dfa dfa) dfa rfl x (compl_dfa dfa).start t at tgo,
        suffices h : t = r,
        finish,
        apply dfa_go_unique tgo rgo,
    },
    {
        rw compl_subset_iff_union,
        rw eq_univ_iff_forall,
        intro x,
        rcases (dfa_go_exists_unique dfa dfa.start x) with ⟨t, tgo, tuniq⟩,
        by_cases tterm : t ∈ dfa.term,
        {
            left,
            use [t, tgo, tterm],
        },
        {
            right,
            use t,
            rw @eq_next_goes_to S Q (compl_dfa dfa) dfa rfl x (compl_dfa dfa).start,
            use tgo,
        }
    },
end


theorem compl_is_aut {S : Type} {L : set (list S)} : dfa_lang L → dfa_lang Lᶜ :=
begin
    rintro ⟨ Q, ⟨ aut, rfl ⟩ ⟩,
    use [Q, compl_dfa aut],
    rwa lang_of_compl_dfa_is_compl_of_lang,
end


def inter_dfa {S Ql Qm : Type} (l : DFA S Ql) (m : DFA S Qm) : DFA S (Ql × Qm) :=
{
    start := (l.start, m.start),
    term := { p : (Ql × Qm) | p.1 ∈ l.term ∧ p.2 ∈ m.term },
    next := λ st : Ql × Qm, λ c : S, (l.next st.1 c, m.next st.2 c)
}


lemma inter_dfa_go 
    {S Ql Qm : Type} 
    (l : DFA S Ql) (m : DFA S Qm) {ql qm rl rm}
     : ∀ {w : list S},
        (go l ql w rl ∧ go m qm w rm) ↔ go (inter_dfa l m) (ql, qm) w (rl, rm):=
begin
    intro w,
    induction w with head tail hyp generalizing ql qm,
    {
        split,
        {
            rintro ⟨lgo, mgo⟩,
            cases lgo,
            cases mgo,
            apply go.finish, 
        },
        {
            rintro intergo,
            cases intergo,
            split; apply go.finish,
        }
    },
    {
        specialize @hyp (l.next ql head) (m.next qm head),
        repeat {rw dfa_go_step_iff at *},
        convert hyp,
    },
end


theorem inter_is_aut 
    {S : Type} {L M : set (list S)} 
    (hl : dfa_lang L) (hm : dfa_lang M) : dfa_lang (L ∩ M) :=
begin
    rcases hl with ⟨ Ql, ⟨ dl, hl ⟩ ⟩,
    rcases hm with ⟨ Qm, ⟨ dm, hm ⟩ ⟩,
    use [Ql × Qm, inter_dfa dl dm],
    ext word,
    split,
    {
        rintro ⟨ xl, xm ⟩,
        rw mem_lang_iff_dfa_acc hl at xl,
        rw mem_lang_iff_dfa_acc hm at xm,
        rcases xl with ⟨lt, lgo, lterm⟩,
        rcases xm with ⟨mt, mgo, mterm⟩,
        use [(lt, mt)],
        split,
        apply (inter_dfa_go dl dm).1,
        use [lgo, mgo],
        use [lterm, mterm],
    },
    {
        rintro ⟨ ⟨ lt, mt⟩, igo, ⟨ lterm, mterm⟩ ⟩,
        have igo := (inter_dfa_go dl dm).2 igo,
        dsimp only [mem_inter_eq],
        rw [mem_lang_iff_dfa_acc hl, mem_lang_iff_dfa_acc hm],
        use [lt, igo.1, lterm],
        use [mt, igo.2, mterm],
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