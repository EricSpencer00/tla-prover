---- MODULE 27_firewall ----
\* benchmark: pyv-firewall

EXTENDS TLAPS, FiniteSetTheorems, TLC

CONSTANT Node

VARIABLE internal
VARIABLE sent
VARIABLE allowed_in

vars == <<internal,sent,allowed_in>>

SendFromInternal(src, dest) == 
    /\ internal[src]
    /\ ~internal[dest]
    /\ sent' = [sent EXCEPT ![src] = @ \cup {dest}]
    /\ allowed_in' = allowed_in \cup {dest}
    /\ UNCHANGED internal

SendToInternal(src, dest) == 
    /\ ~internal[src]
    /\ internal[dest]
    /\ src \in allowed_in
    /\ sent' = [sent EXCEPT ![src] = @ \cup {dest}]
    /\ UNCHANGED <<internal, allowed_in>>

Init == 
    /\ internal \in [Node -> BOOLEAN]
    /\ sent = [n \in Node |-> {}]
    /\ allowed_in = {}

Next == 
    \/ \E s,t \in Node : SendFromInternal(s,t)
    \/ \E s,t \in Node : SendToInternal(s,t)

Inv == 
    \A s,d \in Node:
        (d \in sent[s] /\ internal[d]) => 
        (\E i \in Node : internal[i] /\ s \in sent[i])

NextUnchanged == UNCHANGED vars

TypeOK ==
    /\ internal \in [Node -> BOOLEAN]
    /\ sent \in [Node -> SUBSET Node]
    /\ allowed_in \in SUBSET Node

Symmetry == Permutations(Node)

\* Inductive strengthening conjuncts
Inv285_1_0_def == \A VARI \in Node : \A VARJ \in Node : \E VARK \in Node : (internal[VARI]) \/ (~(VARJ \in sent[VARJ]))
Inv201_1_1_def == \A VARI \in Node : \A VARJ \in Node : \E VARK \in Node : (VARJ \in sent[VARK]) \/ (~(VARJ \in allowed_in))
Inv370_1_2_def == \A VARI \in Node : \A VARJ \in Node : \E VARK \in Node : ~(VARI \in allowed_in) \/ (~(internal[VARI]))
Inv3144_2_3_def == \A VARI \in Node : \A VARJ \in Node : \E VARK \in Node : (internal[VARI]) \/ ((internal[VARJ])) \/ (~(VARI \in sent[VARJ]))

\* The inductive invariant candidate.
IndAuto ==
  /\ TypeOK
  /\ Inv
  /\ Inv285_1_0_def
  /\ Inv201_1_1_def
  /\ Inv370_1_2_def
  /\ Inv3144_2_3_def

ASSUME NodeNonEmpty == Node # {}
ASSUME NodeFinite == IsFiniteSet(Node)

THEOREM Inductiveness == IndAuto /\ Next => IndAuto'BY SMT, SetExtensionality
====