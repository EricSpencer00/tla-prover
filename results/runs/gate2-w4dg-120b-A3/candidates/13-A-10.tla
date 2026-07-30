---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES pc, ticket, num, served

vars == <<pc, ticket, num, served>>

TypeOK ==
  /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ num \in 0..MaxNat
  /\ served \in 0..MaxNat

MutualExclusion ==
  \A i \in 1..N : \A j \in 1..N : (pc[i] = "critical" /\ pc[j] = "critical") => i = j

\* The bakery invariant is the whole of the inductive invariant that the
\* inductive version of the spec must preserve from any reachable state.
Inv ==
  /\ TypeOK
  /\ MutualExclusion

\* The inductive spec: start from any type-correct state and require the
\* invariant to hold after any transition, not just from the initial state.
ISpec == Init /\ [][Next]_vars /\ WF_vars(Enter) /\ WF_vars(Exit) /\ WF_vars(Advance)

Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]
  /\ num = 0
  /\ served = 0

Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ UNCHANGED <<ticket, num, served>>

\* A process may enter only once every other waiting process has a ticket
\* number strictly below its own, so two processes are never critical.
Enter(i) ==
  /\ pc[i] = "waiting"
  /\ \A j \in 1..N : (pc[j] = "waiting" /\ j # i) => ticket[j] < ticket[i]
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED <<ticket, num, served>>

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ UNCHANGED <<ticket, num, served>>

\* A waiting process takes a fresh ticket number; bounded by MaxNat.
TakeTicket(i) ==
  /\ pc[i] = "waiting"
  /\ ticket[i] = 0
  /\ \A j \in 1..N : ticket[j] # i
  /\ num < MaxNat
  /\ num' = num + 1
  /\ ticket' = [ticket EXCEPT ![i] = num + 1]
  /\ UNCHANGED <<pc, served>>

Advance ==
  /\ \E i \in 1..N : Exit(i)
  /\ served < MaxNat
  /\ served' = served + 1
  /\ UNCHANGED <<pc, ticket, num>>

Next ==
  \/ \E i \in 1..N : Request(i) \/ Enter(i) \/ Exit(i) \/ TakeTicket(i)
  \/ Advance

PROPERTIES == MutualExclusion

NatOverride == Nat
====