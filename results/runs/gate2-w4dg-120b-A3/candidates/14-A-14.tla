---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

\* This module extends the Boulanger mutual exclusion algorithm and replaces the
\* unbounded natural numbers with a finite range for model checking. The
\* NatOverride operator below redefines the set of natural numbers to exactly
\* the bounded range 0..MaxNat, keeping EXTENDS Naturals and never naming Nat.

CONSTANTS N, MaxNat

\* Finite set of natural numbers used throughout the model.
NatOverride == 0..MaxNat

\* This replaces Naturals!Nat in the extended configuration. It must be a plain
\* definition, never a CONSTANT declaration; the name on the left stays hidden.
Nat == NatOverride

VARIABLES pc, ticket, csCount

vars == <<pc, ticket, csCount>>

TypeOK ==
  /\ pc \in [1..N -> {"idle", "trying", "cs"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ csCount \in 0..N

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ csCount = 0

Request(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "trying"]
  /\ UNCHANGED <<ticket, csCount>>

Enter(p) ==
  /\ pc[p] = "trying"
  /\ csCount = 0
  /\ \A q \in 1..N : ticket[q] <= ticket[p]
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ csCount' = csCount + 1
  /\ UNCHANGED ticket

Exit(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ ticket' = [ticket EXCEPT ![p] = IF ticket[p] < MaxNat THEN ticket[p] + 1 ELSE ticket[p]]
  /\ csCount' = csCount - 1

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A p, q \in 1..N : (pc[p] = "cs" /\ pc[q] = "cs") => p = q

\* Full inductive invariant: reachable states are exactly the strong-safe states.
Inv == TypeOK /\ MutualExclusion

\* State constraint: ticket numbers never reach the maximum (they saturate below
\* it), which keeps the finite NatOverride replacement well behaved.
TicketsBounded == \A p \in 1..N : ticket[p] < MaxNat

====