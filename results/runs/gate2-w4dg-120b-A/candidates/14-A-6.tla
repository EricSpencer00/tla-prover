---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES ticket, active, served
vars == <<ticket, active, served>>

Init ==
  /\ ticket = [p \in 1..N |-> 0]
  /\ active = [p \in 1..N |-> FALSE]
  /\ served = [p \in 1..N |-> 0]

Request(p) ==
  /\ ~active[p]
  /\ active' = [active EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<ticket, served>>

Enter(p) ==
  /\ active[p]
  /\ ticket' = [ticket EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<active, served>>

Exit(p) ==
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ served' = [served EXCEPT ![p] = @ + 1]
  /\ UNCHANGED ticket

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p \in 1..N : active[p] => served[p] = 0

TypeOK ==
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ active \in [1..N -> BOOLEAN]
  /\ served \in [1..N -> 0..MaxNat]

Inv ==
  /\ TypeOK
  /\ \A p \in 1..N : active[p] => ticket[p] = served[p] + 1

StateBound == \A p \in 1..N : ticket[p] < MaxNat

====