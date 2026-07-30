---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs, want, ticket, nextTicket

vars == <<cs, want, ticket, nextTicket>>

TypeOK ==
  /\ cs \in [1..N -> BOOLEAN]
  /\ want \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ cs = [i \in 1..N |-> FALSE]
  /\ want = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ nextTicket = 0

Request(i) ==
  /\ ~want[i]
  /\ want' = [want EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ UNCHANGED <<cs, nextTicket>>

Acquire(i) ==
  /\ want[i]
  /\ \A j \in 1..N : ~cs[j]
  /\ ticket[i] < nextTicket
  /\ cs' = [cs EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<want, ticket, nextTicket>>

Release(i) ==
  /\ cs[i]
  /\ cs' = [cs EXCEPT ![i] = FALSE]
  /\ want' = [want EXCEPT ![i] = FALSE]
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE nextTicket
  /\ UNCHANGED ticket

Next ==
  \/ \E i \in 1..N : Request(i)
  \/ \E i \in 1..N : Acquire(i)
  \/ \E i \in 1..N : Release(i)

Spec ==
  /\ Init
  /\ [][Next]_vars

MutualExclusion ==
  \A i, j \in 1..N : (cs[i] /\ cs[j]) => i = j

Inv ==
  TypeOK /\ MutualExclusion

StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====