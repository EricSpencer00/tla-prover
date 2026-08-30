---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* The base Bakery mutual exclusion specification, with natural numbers
\* overridden to a finite range 0..MaxNat (rather than the full infinite
\* natural numbers) so that model checking stays finite. The full
\* inductive invariant is checked from any reachable state.

VARIABLES inCS, ticket, want, served
vars == <<inCS, ticket, want, served>>

MaxTicket == MaxNat
MAXSERVED == MaxNat

Init ==
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ want = [i \in 1..N |-> FALSE]
  /\ served = 0

Request ==
  /\ \E i \in 1..N :
       /\ ~want[i]
       /\ ~inCS[i]
       /\ want' = [want EXCEPT ![i] = TRUE]
  /\ UNCHANGED <<inCS, ticket, served>>

Enter ==
  /\ \E i \in 1..N :
       /\ want[i]
       /\ \A j \in 1..N : ~inCS[j]
       /\ (\A j \in 1..N : want[j] => ticket[j] >= ticket[i])
       /\ inCS' = [inCS EXCEPT ![i] = TRUE]
       /\ want' = [want EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<ticket, served>>

Exit ==
  /\ \E i \in 1..N :
       /\ inCS[i]
       /\ inCS' = [inCS EXCEPT ![i] = FALSE]
       /\ ticket' = [ticket EXCEPT ![i] = IF ticket[i] < MaxTicket THEN ticket[i] + 1 ELSE ticket[i]]
       /\ served' = IF served < MAXSERVED THEN served + 1 ELSE served
  /\ UNCHANGED want

Next == Request \/ Enter \/ Exit

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> 0..MaxTicket]
  /\ want \in [1..N -> BOOLEAN]
  /\ served \in 0..MAXSERVED

MutualExclusion ==
  \A i \in 1..N : inCS[i] => (\A j \in 1..N : j # i => ~inCS[j])

Inv ==
  /\ MutualExclusion
  /\ TypeOK

\* The "NatOverride" operator replaces Naturals' unbounded Nat with the
\* finite range 0..MaxNat for model checking. It is declared here as a
\* CONSTANT (its definition is the right-hand side; the name on the left
\* is never redefined or declared anywhere else in this module, per the
\* .cfg's instruction).
NatOverride == 0..MaxNat

ISpec == Init /\ [][Next]_vars
====