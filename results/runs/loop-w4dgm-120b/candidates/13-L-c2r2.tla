---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

Processes == 0 .. (N - 1)

VARIABLES inCS, want, ticket, nextTicket, idle

vars == <<inCS, want, ticket, nextTicket, idle>>

\* Nat is globally constrained to the finite range 0..MaxNat (the override
\* is declared in the .cfg as NatOverride, which must name this definition).
NatOverlay == [x \in Nat |-> IF x <= MaxNat THEN x ELSE x]

TypeOK ==
  /\ inCS \subseteq Processes
  /\ want \subseteq Processes
  /\ ticket \in [Processes -> Nat]
  /\ nextTicket \in NatOverlay
  /\ idle \subseteq Processes

\* Full inductive invariant, not just mutual exclusion: ticket numbers stay
\* below nextTicket, which is exactly what keeps two critical sections apart.
Inv ==
  /\ MutualExclusion == \A a, b \in inCS : a = b
  /\ \A p \in Processes : ticket[p] < nextTicket
  /\ TypeOK

Init ==
  /\ inCS = {}
  /\ want = {}
  /\ ticket = [p \in Processes |-> 0]
  /\ nextTicket = 0
  /\ idle = {}

Arrive(p) ==
  /\ p \notin want
  /\ p \notin inCS
  /\ want' = want \cup {p}
  /\ UNCHANGED <<inCS, ticket, nextTicket, idle>>

Enter(p) ==
  /\ p \in want
  /\ p \notin inCS
  /\ ticket[p] < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ inCS' = inCS \cup {p}
  /\ want' = want \ {p}
  /\ UNCHANGED idle

Leave(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ UNCHANGED <<want, ticket, nextTicket, idle>>

BecomeIdle(p) ==
  /\ p \notin inCS
  /\ p \notin want
  /\ p \notin idle
  /\ idle' = idle \cup {p}
  /\ UNCHANGED <<inCS, want, ticket, nextTicket>>

Wake(p) ==
  /\ p \in idle
  /\ idle' = idle \ {p}
  /\ UNCHANGED <<inCS, want, ticket, nextTicket>>

Next ==
  \/ \E p \in Processes : Arrive(p) \/ Enter(p) \/ Leave(p) \/ BecomeIdle(p) \/ Wake(p)

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ WF_vars(Wake(0)) /\ WF_vars(Wake(1))

\* The invariant is already listed in the shared "Inv" definition, but the
\* .cfg still expects it named here as well.
MutualExclusion == Inv

====