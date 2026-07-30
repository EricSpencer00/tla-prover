---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* The boat may only ever carry one or two people, never empty and never more than its capacity.
BoatCap == 2
People == Missionaries \cup Cannibals

Banks == {"east", "west"}
\* bankOf is a derived view of the distribution map; the two views move together.
bankOf[p \in People] == CHOOSE b \in Banks : p \in location[b]

VARIABLES boatAt, location

vars == <<boatAt, location>>

TypeOK ==
  /\ boatAt \in Banks
  /\ location \in [Banks -> SUBSET People]

Init ==
  /\ boatAt = "east"
  /\ location = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A bank is safe when it either has no missionaries or the cannibals do not outnumber them.
BankSafe(b) ==
  LET ms == Cardinality(Missionaries \cap location[b])
      cs == Cardinality(Cannibals \cap location[b])
  IN (ms = 0) \/ (cs <= ms)

\* Move(p) lets exactly one person board and cross; Move(p, q) lets a pair cross.
Move(p) ==
  /\ p \in location[boatAt]
  /\ Cardinality({r \in People : r \in location[boatAt] /\ r \in {p}}) = 1
  /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
  /\ location' = [location EXCEPT ![boatAt] = @ \ {p}, ![boatAt' = "east"] = @ \cup {p}]
  /\ /\ BankSafe("east") /\ BankSafe("west")

Move(p, q) ==
  /\ p \in location[boatAt] /\ q \in location[boatAt] /\ p # q
  /\ Cardinality({r \in People : r \in location[boatAt] /\ r \in {p, q}}) = 2
  /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
  /\ location' = [location EXCEPT ![boatAt] = @ \ {p, q}, ![boatAt' = "east"] = @ \cup {p, q}]
  /\ /\ BankSafe("east") /\ BankSafe("west")

Next == \E p \in People : Move(p) \/ \E q \in People : Move(p, q)

Spec == Init /\ [][Next]_vars

\* Solution: the east bank is empty, so the puzzle is solved.
Solution == Cardinality(location["east"]) = 0

====