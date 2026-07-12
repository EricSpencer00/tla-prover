---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, MaxNat, Nat

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TypeOK ==  /\ N \in Nat
           /\ MaxNat \in Nat
           /\ N >= 1
           /\ MaxNat >= 1

\* ----------------------------------------------------------------------
\* State variables (the same as in the Bakery module, but with Nat replaced)
\* ----------------------------------------------------------------------
VARIABLES owner, label, waiting, n

\* The Nat set is overridden to the finite range 0..MaxNat
Nat == 0..MaxNat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == /\ owner = {}
        /\ label = [i \in 1..N |-> 0]
        /\ waiting = [i \in 1..N |-> 0]
        /\ n = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
TakeTurn(i) ==
  /\ i \in 1..N
  /\ n' = n + 1
  /\ waiting' = [waiting EXCEPT ![i] = n']
  /\ UNCHANGED << owner, label >>

StartCritical(i) ==
  /\ i \in 1..N
  /\ waiting[i] > 0
  /\ \A j \in 1..N : j # i => 
            (waiting[i] < waiting[j]) \/ 
            /\ waiting[i] = waiting[j] /\ i < j
  /\ owner' = owner \cup {i}
  /\ waiting' = [waiting EXCEPT ![i] = 0]
  /\ UNCHANGED << label, n >>

ExitCritical(i) ==
  /\ i \in 1..N
  /\ i \in owner
  /\ owner' = owner \ {i}
  /\ UNCHANGED << label, waiting, n >>

\* ----------------------------------------------------------------------
\* Next-state relation (any process can take a turn, start critical, or exit)
\* ----------------------------------------------------------------------
Next ==
  \E i \in 1..N : 
      (TakeTurn(i) \/ StartCritical(i) \/ ExitCritical(i))

\* ----------------------------------------------------------------------
\* Specification (inductive, starting from any type-correct state)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<owner, label, waiting, n>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
MutualExclusion == \A i, j \in owner : i = j
TypeOK == /\ owner \subseteq 1..N
          /\ \A i \in 1..N : label[i] \in Nat
          /\ \A i \in 1..N : waiting[i] \in Nat
          /\ n \in Nat
Inv == MutualExclusion /\ TypeOK

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg
\* ----------------------------------------------------------------------
ISpec == Spec
INVARIANTS == {MutualExclusion, TypeOK, Inv}
```
====