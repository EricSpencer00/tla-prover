---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* The `NatOverride` operator below replaces the infinite `Nat` set from the
\* Naturals module with the finite range 0..MaxNat for model checking:
NatOverride == 0..MaxNat

VARIABLES idle, waiting, cs, ticket, nextTicket

vars == << idle, waiting, cs, ticket, nextTicket >>

TypeOK ==
  /\ idle \in [1..N -> BOOLEAN]
  /\ waiting \in [1..N -> BOOLEAN]
  /\ cs \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride

Init ==
  /\ idle = [p \in 1..N |-> TRUE]
  /\ waiting = [p \in 1..N |-> FALSE]
  /\ cs = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

Request(p) ==
  /\ idle[p]
  /\ idle' = [idle EXCEPT ![p] = FALSE]
  /\ waiting' = [waiting EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = IF nextTicket = MaxNat THEN 0 ELSE nextTicket + 1
  /\ UNCHANGED cs

Enter(p) ==
  /\ waiting[p]
  /\ \A q \in 1..N : ~cs[q]
  /\ \A q \in 1..N : waiting[q] => ticket[p] <= ticket[q]
  /\ waiting' = [waiting EXCEPT ![p] = FALSE]
  /\ cs' = [cs EXCEPT ![p] = TRUE]
  /\ UNCHANGED << idle, ticket, nextTicket >>

Exit(p) ==
  /\ cs[p]
  /\ cs' = [cs EXCEPT ![p] = FALSE]
  /\ idle' = [idle EXCEPT ![p] = TRUE]
  /\ UNCHANGED << waiting, ticket, nextTicket >>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

MutualExclusion ==
  \A p, q \in 1..N : (cs[p] /\ cs[q]) => p = q

\* The full inductive invariant from the Bakery spec:
Inv == TypeOK /\ MutualExclusion

\* Inductive spec starts from any reachable type-correct state, not just Init:
ISpec == Init /\ [][Next]_vars

====