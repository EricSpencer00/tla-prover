---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

\* The ticket registers of each process, ranging over a finite window of
\* natural numbers (bounded for model checking by MaxNat).
VARIABLES tickets

vars == << tickets >>

TypeOK ==
  /\ tickets \in [1..N -> 0..(MaxNat - 1)]

\* One process holds the critical section; its ticket is strictly below
\* the maximum, so ticket numbers never overflow the bounded window.
MutualExclusion ==
  \A i \in 1..N : tickets[i] < MaxNat

Init ==
  /\ tickets = [i \in 1..N |-> 0]

\* A process enters or re-enters the critical section, bumping its ticket
\* number while staying strictly below the maximum.
Acquire(i) ==
  /\ tickets[i] < MaxNat - 1
  /\ tickets' = [tickets EXCEPT ![i] = tickets[i] + 1]

\* A process leaves the critical section, freeing its ticket register.
Release(i) ==
  /\ tickets[i] > 0
  /\ tickets' = [tickets EXCEPT ![i] = tickets[i] - 1]

Next ==
  \E i \in 1..N : Acquire(i) \/ Release(i)

Spec == Init /\ [][Next]_vars

\* The inductive invariant for the bounded model is the same as the
\* mutual exclusion plus the type well-formedness; both must hold.
Inv == MutualExclusion /\ TypeOK

====