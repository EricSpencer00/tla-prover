---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat, Nat

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

TypeOK ==
  /\ inCS \subseteq 1..N
  /\ want \in SUBSET (1..N)
  /\ ticket \in [1..N -> Nat]
  /\ nextTicket \in Nat

Init ==
  /\ inCS = {}
  /\ want = {}
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

Request(p) ==
  /\ p \notin want
  /\ p \notin inCS
  /\ want' = want \cup {p}
  /\ UNCHANGED <<inCS, ticket, nextTicket>>

Enter(p) ==
  /\ p \in want
  /\ p \notin inCS
  /\ \A q \in inCS : ticket[p] < ticket[q]
  /\ inCS' = inCS \cup {p}
  /\ want' = want \ {p}
  /\ UNCHANGED <<ticket, nextTicket>>

Exit(p) ==
  /\ p \in inCS
  /\ inCS' = inCS \ {p}
  /\ UNCHANGED <<want, ticket, nextTicket>>

Bump(p) ==
  /\ p \notin inCS
  /\ nextTicket < MaxNat
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ nextTicket' = nextTicket + 1
  /\ UNCHANGED <<inCS, want>>

Next ==
  \/ \E p \in 1..N: Request(p)
  \/ \E p \in 1..N: Enter(p)
  \/ \E p \in 1..N: Exit(p)
  \/ \E p \in 1..N: Bump(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p, q \in inCS : p = q

Inv ==
  /\ nextTicket <= MaxNat
  /\ \A p \in 1..N : ticket[p] <= MaxNat

====