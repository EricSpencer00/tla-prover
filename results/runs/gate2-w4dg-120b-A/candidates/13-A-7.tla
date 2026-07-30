---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES pc, ticket, number, served

vars == <<pc, ticket, number, served>>

\* The ticket numbers are drawn from the overridden, bounded natural number
\* range 0..MaxNat, so the state space stays finite for model checking.
Range == 0..MaxNat

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ number = 0
  /\ served = [p \in 1..N |-> 0]

\* A process requests entry by taking the next ticket number in the range.
Request(p) ==
  /\ pc[p] = "idle"
  /\ number' = (number + 1) % (MaxNat + 1)
  /\ ticket' = [ticket EXCEPT ![p] = number]
  /\ pc' = [pc EXCEPT ![p] = "waiting"]
  /\ UNCHANGED served

\* A waiting process enters the critical section when it holds the lowest
\* ticket number among all currently waiting processes.
Enter(p) ==
  /\ pc[p] = "waiting"
  /\ \A q \in 1..N : (pc[q] = "waiting") => (ticket[p] <= ticket[q])
  /\ pc' = [pc EXCEPT ![p] = "critical"]
  /\ UNCHANGED <<ticket, number, served>>

\* A process leaves the critical section.
Exit(p) ==
  /\ pc[p] = "critical"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ served' = [served EXCEPT ![p] = (served[p] + 1) % (MaxNat + 1)]
  /\ UNCHANGED <<ticket, number>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

MutualExclusion ==
  \A p, q \in 1..N : (pc[p] = "critical" /\ pc[q] = "critical") => (p = q)

TypeOK ==
  /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> Range]
  /\ number \in Range
  /\ served \in [1..N -> Range]

Inv ==
  /\ MutualExclusion
  /\ TypeOK
  /\ \A p \in 1..N :
       /\ pc[p] \in {"idle", "waiting", "critical"}
       /\ ticket[p] \in Range
       /\ served[p] \in Range
  /\ number \in Range

Spec == Init /\ [][Next]_vars
ISpec == Spec /\ Inv

====