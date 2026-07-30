---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Override the built-in Nat with a finite version so the model is checkable.
\* EXTENDS Naturals is kept for all the other operators we rely on.
NatOverride == {n \in 0 .. MaxNat : TRUE}

VARIABLES pc, ticket, holder

vars == <<pc, ticket, holder>>

TypeOK ==
  /\ pc \in [1 .. N -> {"idle", "waiting", "critical"}]
  /\ ticket \in [1 .. N -> 0 .. MaxNat]
  /\ holder \in 0 .. N

Init ==
  /\ pc = [i \in 1 .. N |-> "idle"]
  /\ ticket = [i \in 1 .. N |-> 0]
  /\ holder = 0

\* Boulanger's request rule: keep ticket numbers below the finite bound.
Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ ticket' = [ticket EXCEPT ![i] = IF ticket[i] < MaxNat THEN ticket[i] + 1 ELSE ticket[i]]
  /\ UNCHANGED holder

Enter(i) ==
  /\ pc[i] = "waiting"
  /\ holder = 0
  /\ \A j \in 1 .. N : ticket[j] >= ticket[i]
  /\ holder' = i
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED ticket

Exit(i) ==
  /\ pc[i] = "critical"
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  /\ holder' = 0
  /\ UNCHANGED ticket

Next == \E i \in 1 .. N : Request(i) \/ Enter(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i \in 1 .. N : (pc[i] = "critical") => (holder = i)

Inv ==
  /\ \A i \in 1 .. N : pc[i] \in {"idle", "waiting", "critical"}
  /\ \A i \in 1 .. N : ticket[i] \in 0 .. MaxNat
  /\ holder \in 0 .. N
  /\ \A i \in 1 .. N : pc[i] = "critical" => (holder = i)

BoundedTickets == \A i \in 1 .. N : ticket[i] < MaxNat

====