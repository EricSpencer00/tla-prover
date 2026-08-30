---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, Satisfiability, MaxTimeout

Operators == {Zenon, Isabelle, CVC3, Yices, veriT, Z3, SPASS, LS4, Satisfiability}

RECURSIVE Occurs(_)
Occurs(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Occurs(S \ {x})

VARIABLES invoked, timeout
vars == <<invoked, timeout>>

TypeOK ==
  /\ invoked \subseteq Operators
  /\ timeout \in 0..MaxTimeout

Spec ==
  /\ invoked = {}
  /\ timeout = 0

Invoke(o) == /\ o \notin invoked
             /\ invoked' = invoked \cup {o}
             /\ UNCHANGED timeout
Adjust(t) == /\ timeout' = t
             /\ UNCHANGED invoked

Init == Spec
Next == \E o \in Operators : Invoke(o) \/ \E t \in 0..MaxTimeout : Adjust(t)

SPECIFICATION == Init /\ [][Next]_vars

Extensionality ==
  \A X, Y \in SUBSET Operators : (FORALL x \in Operators : (x \in X) <=> (x \in Y)) => X = Y
NoAllValues == \A x \in Operators : x \notin Operators
INVARIANTS == Extensionality
PROPERTIES == NoAllValues
====