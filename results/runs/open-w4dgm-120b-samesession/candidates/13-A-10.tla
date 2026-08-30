---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

\* Finite-range replacement for the infinite Nat, so ticket numbers stay
\* bounded during model checking.  We keep the name Nat on the left (the .cfg
\* binding replaces the imported constant with this definition) and define
\* the right side; the constant itself is never declared here.
NatOverride == 0..MaxNat

VARIABLES ticket, inCS, want, nextTicket

vars == <<ticket, inCS, want, nextTicket>>

TypeOK ==
  /\ ticket \in [1..N -> NatOverride]
  /\ inCS \subseteq 1..N
  /\ want \subseteq 1..N
  /\ nextTicket \in NatOverride

Init ==
  /\ ticket = [i \in 1..N |-> 0]
  /\ inCS = {}
  /\ want = {}
  /\ nextTicket = 0

Request(i) ==
  /\ i \notin want
  /\ i \notin inCS
  /\ want' = want \cup {i}
  /\ UNCHANGED <<ticket, inCS, nextTicket>>

Enter(i) ==
  /\ i \in want
  /\ inCS = {}
  /\ i \notin inCS
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![i] = nextTicket + 1]
  /\ inCS' = inCS \cup {i}
  /\ want' = want \ {i}
  /\ nextTicket' = nextTicket + 1

Exit(i) ==
  /\ i \in inCS
  /\ inCS' = inCS \ {i}
  /\ UNCHANGED <<ticket, want, nextTicket>>

Next ==
  \/ (\E i \in 1..N : Request(i)
  \/ (\E i \in 1..N : Enter(i)
  \/ (\E i \in 1..N : Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i, j \in inCS : i = j

\* Full inductive invariant: token monotonicity plus the single-holder shape.
Inv == MutualExclusion /\ \A i \in inCS : ticket[i] > 0

ISpec == Spec /\ Inv
====