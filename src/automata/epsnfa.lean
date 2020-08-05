import data.set.basic
import data.set.finite
import automata.nfa

open set nfa

namespace epsnfa

variables {S Q : Type}


structure epsNFA (S : Type) (Q : Type) :=
    (start : Q) -- starting state
    (term : set Q) -- terminal states
    (next : Q → S → set Q) -- transitions
    (eps : Q → set Q) -- eps-transitions


end epsnfa