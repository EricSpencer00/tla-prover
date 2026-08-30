---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* A person is either a missionary or a cannibal, never both.
People == Missionaries \union Cannibals

Banks == {"east", "west"}
\* Population is the number of people on each bank; SafeStat(e) is the safety
\* property the puzzle is built around, expressed pointwise over banks.
VARIABLES boatAt, loiter, movers, lastMove

vars == <<boatAt, loiter, movers, lastMove>>

\* Count the population of a bank; used inside the bank-guarded safety check.
Pop(b, S) == Cardinality({p \in S : loiter[p] = b})

TypeOK ==
  /\ boatAt \in Banks
  /\ loiter \in [People -> Banks]
  /\ movers \in SUBSET People
  /\ lastMove \in [from: Banks, to: Banks]

Init ==
  /\ boatAt = "east"
  /\ loiter = [p \in People |-> "east"]
  /\ movers = {}
  /\ lastMove = [from |-> "east", to |-> "west"]

\* SafeStat(e) is the bank's local safety check: no missionaries present, or
\* cannibals do not outnumber them. It is re-evaluated after every move.
\* boatAt toggles the docked bank, so the boat can never travel empty.
Board ==
  /\ movers = {}
  /\ Cardinality(movers) < 2
  /\ \E p \in People :
       /\ loiter[p] = boatAt
       /\ loiter' = [loiter EXCEPT ![p] = "none"]
       /\ movers' = movers \union {p}
  /\ UNCHANGED <<boatAt, lastMove>>

Cross ==
  /\ movers # {}
  /\ \E dest \in Banks :
       /\ dest # boatAt
       /\ Cardinality(movers) >= 1
       /\ \A q \in People : loiter' = [loiter EXCEPT ![q] = IF q \in movers THEN dest ELSE @]
       /\ lastMove' = [from |-> boatAt, to |-> dest]
       /\ \A b \in Banks : Pop(b, People) <= 3 /\ (Pop(b, Missionaries) = 0 \/ Pop(b, Cannibals) <= Pop(b, Missionaries))
       /\ boatAt' = dest
  /\ movers' = {}

Disembark ==
  /\ \E p \in People :
       /\ loiter[p] = "none"
       /\ loiter' = [loiter EXCEPT ![p] = boatAt]
  /\ UNCHANGED <<boatAt, movers, lastMove>>

Next == Board \/ Cross \/ Disembark

Solution == \A p \in Missionaries : loiter[p] = "west"

Spec == Init /\ [][Next]_vars

\* Missionaries safe: never outnumbered by cannibals on any bank that has them.
SafeStat(e) == Pop(e, Missionaries) = 0 \/ Pop(e, Cannibals) <= Pop(e, Missionaries)
TypeOK2 == \A e \in Banks : SafeStat(e)

\* Boat occupancy is always one or two people per crossing (never empty).
\* The "never empty" part is what prevents the boat crossing without movers.
OccupancyBound == 1 <= Cardinality(movers) /\ Cardinality(movers) <= 2

====