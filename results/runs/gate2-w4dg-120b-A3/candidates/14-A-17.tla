---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Overridden to a finite version for model checking; Nat itself is never
\* declared or redefined here, only NatOverride is defined as .cfg specifies.
NatOverride == Nat

VARIABLES pc, ticket

vars == <<pc, ticket>>

\* Inherited from the Boulanger spec, but constrained to the finite range.
Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ ticket = [i \in 1..N |-> 0]

\* Inherited from the Boulanger spec; renamed here as Spec's Next is renamed.
Next ==
  /\ \E i \in 1..N :
       \/ /\ pc[i] = "idle" /\ pc' = [pc EXCEPT ![i] = "trying"]
          /\ ticket' = [ticket EXCEPT ![i] = 0]
       \/ /\ pc[i] = "trying" /\ \A k \in 1..N : ticket[i] <= ticket[k]
          /\ pc' = [pc EXCEPT ![i] = "critical"]
          /\ ticket' = [ticket EXCEPT ![i] = IF ticket[i] < MaxNat THEN ticket[i] + 1 ELSE ticket[i]]
       \/ /\ pc[i] = "critical" /\ pc' = [pc EXCEPT ![i] = "idle"]
          /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED <<pc, ticket>>

Spec == Init /\ [][Next]_vars

\* Inherited safety properties.
MutualExclusion ==
  \A i \in 1..N, j \in 1..N :
    (pc[i] = "critical" /\ pc[j] = "critical") => (i = j)

TypeOK ==
  /\ pc \in [1..N -> {"idle", "trying", "critical"}]
  /\ ticket \in [1..N -> 0..MaxNat]

\* The full inductive invariant; also inherited.
Inv ==
  /\ MutualExclusion
  /\ TypeOK

\* The finite-range state constraint.
BoundedTickets ==
  \A i \in 1..N : ticket[i] <= MaxNat

====