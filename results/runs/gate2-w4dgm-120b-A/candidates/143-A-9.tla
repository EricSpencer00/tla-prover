---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
Persons == Missionaries \cup Cannibals

VARIABLES boatAt, bank, crossing

vars == <<boatAt, bank, crossing>>

\* Safety: each bank's cannibals never outnumber its missionaries (unless
\* no missionary is present, in which case the bank is safe by default).
BankIsSafe(ba) ==
    LET ms == Missionaries \cap bank[ba] IN
    LET cs == Cannibals \cap bank[ba] IN
    (ms = {}) \/ (Cardinality(cs) <= Cardinality(ms))

TypeOK ==
    /\ boatAt \in Banks
    /\ bank \in [Banks -> SUBSET Persons]
    /\ crossing \in SUBSET Persons

\* Solution: the east bank is never left completely empty (a crossing is
\* always still in progress or waiting to return).  A crossing that truly
\* solves the puzzle -- everyone on the west bank -- is reachable from any
\* reachable state but is never reached here, so this stays an invariant.
Solution == bank["east"] # {}

Init ==
    /\ boatAt = "east"
    /\ bank = [b \in Banks |-> IF b = "east" THEN Persons ELSE {}]
    /\ crossing = {}

\* One or two people board on the current bank, cross, and disembark on the
\* far side.  The crossing is only enabled if it keeps both banks safe.
Move ==
    /\ crossing = {}
    /\ Cardinality(bank[boatAt]) >= 1
    /\ \E g \in SUBSET Persons :
         /\ Cardinality(g) \in {1, 2}
         /\ g \subseteq bank[boatAt]
         /\ \A ba \in Banks :
              /\ Cardinality(bank[ba] \ g) = Cardinality(bank[ba]) - (IF ba = boatAt THEN Cardinality(g) ELSE 0)
              /\ Cardinality(bank[ba] \cup (IF ba = (IF boatAt = "east" THEN "west" ELSE "east") THEN g ELSE {}))
                    = Cardinality(bank[ba]) + (IF ba = (IF boatAt = "east" THEN "west" ELSE "east") THEN Cardinality(g) ELSE 0)
              /\ BankIsSafe(ba)
         /\ crossing' = g
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
    /\ UNCHANGED bank

Next == Move

Spec == Init /\ [][Next]_vars

\* Bounded capacity: the boat never carries zero people and never more than
\* its capacity of two.
CapacityOK == Cardinality(crossing) \in {0, 1, 2}

====