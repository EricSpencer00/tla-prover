---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

ASSUME N \in Nat \ {0}
ASSUME MaxNat \in Nat

VARIABLES ticket, next, inCS, served
vars == <<ticket, next, inCS, served>>

MaxTicket == MaxNat

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ next = 0
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ served = 0

Enter(i) ==
  /\ ~inCS[i]
  /\ next < MaxTicket
  /\ ticket[i] = 0
  /\ next' = next + 1
  /\ ticket' = [ticket EXCEPT ![i] = next + 1]
  /\ UNCHANGED <<inCS, served>>

Acquire(i) ==
  /\ ~inCS[i]
  /\ ticket[i] # 0
  /\ \A j \in 1..N : (~inCS[j] \/ ticket[j] >= ticket[i])
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<ticket, next, served>>

Exit(i) ==
  /\ inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ served' = (served + 1) % (MaxTicket + 1)
  /\ UNCHANGED next

Next == \E i \in 1..N : Enter(i) \/ Acquire(i) \/ Exit(i)

Spec == Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ ticket \in [1..N -> 0..MaxTicket]
  /\ next \in 0..MaxTicket
  /\ inCS \in [1..N -> BOOLEAN]
  /\ served \in 0..MaxTicket

MutualExclusion == \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

Inv ==
  /\ TypeOK
  /\ MutualExclusion

ISpec == Spec
====