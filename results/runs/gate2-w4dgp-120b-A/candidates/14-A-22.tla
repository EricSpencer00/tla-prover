---- MODULE MCBoulanger ----
EXTENDS Integers, Naturals, FiniteSets

CONSTANTS N, MaxNat

ASSUME N \in Nat /\ N >= 2 /\ MaxNat \in Nat /\ MaxNat >= 2

VARIABLES pc, ticket, inCS, count

vars == <<pc, ticket, inCS, count>>

\* The finite override of Nat (see the .cfg) is a semantic plug-in: every
\* occurrence of the natural-number type in the inherited Boulanger spec
\* must be interpreted as a number in the bounded range 0..MaxNat instead of
\* the full infinite set. The plug-in replaces the name Nat with NatOverride
\* but leaves the source text untouched.

Bump(x) == IF x < MaxNat THEN x + 1 ELSE x

Init ==
  /\ pc = [p \in 1..N |-> "idle"]
  /\ ticket = [p \in 1..N |-> 0]
  /\ inCS = {}
  /\ count = 0

Request(p) ==
  /\ pc[p] = "idle"
  /\ ticket' = [ticket EXCEPT ![p] = Bump(@)]
  /\ pc' = [pc EXCEPT ![p] = "trying"]
  /\ UNCHANGED <<inCS, count>>

Enter(p) ==
  /\ pc[p] = "trying"
  /\ \A q \in inCS : ticket[p] <= ticket[q]
  /\ inCS' = inCS \cup {p}
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED <<ticket, count>>

Exit(p) ==
  /\ pc[p] = "cs"
  /\ inCS' = inCS \ {p}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ count' = IF count < MaxNat THEN count + 1 ELSE count
  /\ UNCHANGED ticket

Next ==
  \/ Enter(1)
  \/ Exit(1)
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 1..N : (pc[p] = "cs") => (p \in inCS)

TypeOK ==
  /\ pc \in [1..N -> {"idle","trying","cs"}]
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ count \in 0..MaxNat

Inv ==
  /\ MutualExclusion
  /\ TypeOK

NoTicketAtMax == \A p \in 1..N : ticket[p] < MaxNat

====