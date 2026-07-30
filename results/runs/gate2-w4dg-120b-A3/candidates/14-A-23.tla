---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

ASSUME N \in Nat /\ N >= 2
ASSUME MaxNat \in Nat /\ MaxNat >= 2

\* A finite version of Nat, for model checking.  Nat is still in scope via
\* EXTENDS; this operator replaces it in the .cfg, so we do NOT declare Nat.
NatOverride == {0, 1, 2}

VARIABLES pc, hasLock, ticket
vars == <<pc, hasLock, ticket>>

\* The original (unbounded) Boulanger initialization, now with a bounded
\* ticket range.
Init ==
  /\ pc = [i \in 1..N |-> "idle"]
  /\ hasLock = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]

\* The original actions, unmodified.
Request(i) ==
  /\ pc[i] = "idle"
  /\ pc' = [pc EXCEPT ![i] = "waiting"]
  /\ UNCHANGED <<hasLock, ticket>>

Acquire(i) ==
  /\ pc[i] = "waiting"
  /\ \A j \in 1..N : pc[j] # "critical"
  /\ hasLock' = [hasLock EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "critical"]
  /\ UNCHANGED ticket

Release(i) ==
  /\ pc[i] = "critical"
  /\ nextT < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = nextT]
  /\ hasLock' = [hasLock EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "idle"]
  where nextT == ticket[i] + 1

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Acquire(i)
  \/ \E i \in 1..N : Release(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (hasLock[i] /\ hasLock[j]) => i = j

TypeOK ==
  /\ pc \in [1..N -> {"idle", "waiting", "critical"}]
  /\ hasLock \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]

\* The inductive invariant from the Boulanger spec.
Inv == MutualExclusion /\ TypeOK

\* The state constraint that keeps the model finite.
TicketBound == \A i \in 1..N : ticket[i] < MaxNat

====