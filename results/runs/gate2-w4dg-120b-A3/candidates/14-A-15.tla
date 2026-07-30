---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES pc, ticket, owner, pads

vars == <<pc, ticket, owner, pads>>

Idle == "idle"
Trying == "trying"
InCS == "cs"
Nxt(t) == IF t < MaxNat THEN t + 1 ELSE t

TypeOK ==
  /\ pc \in [1..N -> {Idle, Trying, InCS}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ owner \in 1..N \cup {0}
  /\ pads \in 0..MaxNat

Init ==
  /\ pc = [i \in 1..N |-> Idle]
  /\ ticket = [i \in 1..N |-> 0]
  /\ owner = 0
  /\ pads = 0

Request(i) ==
  /\ pc[i] = Idle
  /\ pc' = [pc EXCEPT ![i] = Trying]
  /\ UNCHANGED <<ticket, owner, pads>>

Take(i) ==
  /\ pc[i] = Trying
  /\ owner = 0
  /\ owner' = i
  /\ ticket' = [ticket EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = InCS]
  /\ UNCHANGED pads

Release(i) ==
  /\ pc[i] = InCS
  /\ owner' = 0
  /\ pc' = [pc EXCEPT ![i] = Idle]
  /\ pads' = Nxt(pads)
  /\ UNCHANGED ticket

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Take(i)
  \/ \E i \in 1..N : Release(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i \in 1..N : pc[i] = InCS => owner = i

Inv ==
  /\ pads <= MaxNat
  /\ \A i \in 1..N : ticket[i] <= MaxNat
  /\ \A i \in 1..N : pc[i] = InCS => owner = i

NatOverride == Nat

====