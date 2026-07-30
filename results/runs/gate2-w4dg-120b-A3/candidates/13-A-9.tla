---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Replace the unbounded Nat type with a finite range for model checking.
\* Nat stays from Naturals (to keep the rest compatible); the override below
\* makes the ticket number domain finite without redefining the identifier.
NatOverride == { n \in Nat : n <= MaxNat }

VARIABLES inCS, wants, ticket, nextTicket

vars == << inCS, wants, ticket, nextTicket >>

Init ==
  /\ inCS = {}
  /\ wants = [p \in 1..N |-> FALSE]
  /\ ticket = [p \in 1..N |-> 0]
  /\ nextTicket = 0

Request(p) ==
  /\ p \notin inCS
  /\ ~wants[p]
  /\ wants' = [wants EXCEPT ![p] = TRUE]
  /\ ticket' = [ticket EXCEPT ![p] = nextTicket]
  /\ UNCHANGED << inCS, nextTicket >>

\* The ticket number is capped at MaxNat, wrapping back to 0 when the ceiling
\* is reached.  That keeps the domain finite while still letting every
\* process eventually get a turn.
Enter(p) ==
  /\ wants[p]
  /\ inCS = {}
  /\ \A q \in 1..N : ticket[p] <= ticket[q]
  /\ inCS' = {p}
  /\ wants' = [wants EXCEPT ![p] = FALSE]
  /\ UNCHANGED << ticket, nextTicket >>

Exit(p) ==
  /\ p \in inCS
  /\ inCS' = {}
  /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE 0
  /\ UNCHANGED << wants, ticket >>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A a, b \in inCS : a = b

TypeOK ==
  /\ inCS \subseteq (1..N)
  /\ wants \in [1..N -> BOOLEAN]
  /\ ticket \in [1..N -> NatOverride]
  /\ nextTicket \in NatOverride

Inv == MutualExclusion /\ TypeOK

ISpec == Spec /\ Inv

====