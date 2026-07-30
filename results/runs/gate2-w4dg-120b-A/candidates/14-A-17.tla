---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES tickets, inCS, wants, nextTicket

vars == <<tickets, inCS, wants, nextTicket>>

TypeOK ==
  /\ tickets \in [1..N -> 0..MaxNat]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ wants \in SUBSET (1..N)
  /\ nextTicket \in 0..MaxNat

Init ==
  /\ tickets = [p \in 1..N |-> 0]
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ wants = {}
  /\ nextTicket = 0

Request(p) ==
  /\ p \notin wants
  /\ ~inCS[p]
  /\ wants' = wants \cup {p}
  /\ UNCHANGED <<tickets, inCS, nextTicket>>

Enter(p) ==
  /\ p \in wants
  /\ \A q \in 1..N : ~inCS[q]
  /\ nextTicket < MaxNat
  /\ tickets' = [tickets EXCEPT ![p] = nextTicket]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ wants' = wants \ {p}
  /\ nextTicket' = nextTicket + 1

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<tickets, wants, nextTicket>>

Next ==
  \/ \E p \in 1..N : Request(p)
  \/ \E p \in 1..N : Enter(p)
  \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  \A p \in 1..N : inCS[p] => (\A q \in 1..N : ~inCS[q] \/ q = p)

Inv ==
  /\ \A p \in 1..N : inCS[p] => (\A q \in 1..N : (inCS[q] => q = p))
  /\ tickets \in [1..N -> 0..MaxNat]

StateConstraint == \A p \in 1..N : tickets[p] < MaxNat

====