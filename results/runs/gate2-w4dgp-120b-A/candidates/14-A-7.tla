---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES pc, ticket, owner, label

vars == <<pc, ticket, owner, label>>

ModNat == 0..MaxNat

TypeOK ==
  /\ pc \in [1..N -> {"idle", "trying", "cs", "done", "ready"}]
  /\ ticket \in [1..N -> ModNat]
  /\ owner \subseteq 1..N
  /\ label \in {"none", "wait"}

Waiting == {p \in 1..N : pc[p] = "trying"}
Request > 0 == CHOOSE p \in Waiting : TRUE

Inv ==
  /\ \A p \in 1..N : pc[p] \in {"idle", "trying", "cs", "done", "ready"}
  /\ \A p \in 1..N : ticket[p] \in ModNat
  /\ owner \subseteq 1..N
  /\ label \in {"none", "wait"}
  /\ label = "none" => owner = {}

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ owner = {}
  /\ label = "none"

Submit(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "trying"]
  /\ UNCHANGED <<ticket, owner, label>>

Enter(p) ==
  /\ pc[p] = "trying"
  /\ owner = {}
  /\ \A q \in 1..N : ticket[p] <= ticket[q]
  /\ owner' = {p}
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<ticket, label>>

Leave(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ owner' = {}
  /\ UNCHANGED <<ticket, label>>

Reset(p) ==
  /\ pc[p] = "done"
  /\ ticket[p] < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = ticket[p] + 1]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<owner, label>>

Wait(p) ==
  /\ pc[p] = "idle"
  /\ label' = "wait"
  /\ UNCHANGED <<pc, ticket, owner>>

Response(p) ==
  /\ pc[p] = "idle"
  /\ label = "wait"
  /\ label' = "none"
  /\ UNCHANGED <<pc, ticket, owner>>

Next ==
  \/ \E p \in 1..N : Submit(p) \/ Enter(p) \/ Leave(p) \/ Reset(p) \/ Response(p)
  \/ Wait(Request)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p, q \in 1..N : (p \in owner /\ q \in owner) => p = q

StateBound == \A p \in 1..N : ticket[p] < MaxNat

====