---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES inCS, served, entrant, bought
vars == <<inCS, served, entrant, bought>>

Init ==
  /\ inCS = {}
  /\ served = 0
  /\ entrant = [p \in 1..N |-> MaxNat + 1]
  /\ bought = 0

Enter(p) ==
  /\ p \notin inCS
  /\ \A q \in 1..N : entrant[q] > p
  /\ inCS' = inCS \cup {p}
  /\ entrant' = [entrant EXCEPT ![p] = p]
  /\ UNCHANGED <<served, bought>>

Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ served' = IF served < MaxNat THEN served + 1 ELSE served
  /\ bought' \in {bought, IF bought < MaxNat THEN bought + 1 ELSE bought}
  /\ UNCHANGED <<entrant>>

Next == \E p \in 1..N : Enter(p) \/ Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p, q \in inCS : p = q
TypeOK ==
  /\ inCS \subseteq 1..N
  /\ served \in 0..MaxNat
  /\ entrant \in [1..N -> 0..(MaxNat + 1)]
  /\ bought \in 0..MaxNat
Inv == MutualExclusion /\ TypeOK

ISpec == Spec
====