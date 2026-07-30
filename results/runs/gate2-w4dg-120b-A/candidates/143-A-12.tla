---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
Board == Missionaries \cup Cannibals \cup {"none"}

VARIABLES boatBank, shore, carrying, crossing

vars == <<boatBank, shore, carrying, crossing>>

\* A bank is safe if it has no missionaries, or if cannibals never outnumber them.
\* The boat always carries one or two people (never empty, never more than two).
\* The goal is to empty the east bank onto the west bank safely.

TypeOK ==
  /\ boatBank \in Banks
  /\ shore \in [Banks -> SUBSET People]
  /\ carrying \in SUBSET People
  /\ crossing \in BOOLEAN
  /\ Cardinality(carrying) \in 1..2

\* An empty carrying set would let the boat cross empty; disallow it.
NoEmptyCarry == carrying # {}

\* Safe iff either no missionaries are present (only cannibals) or cannibals
\* do not outnumber missionaries.
BankSafe(b) ==
  \/ (shore[b] \cap Missionaries) = {}
  \/ Cardinality(shore[b] \cap Cannibals) <= Cardinality(shore[b] \cap Missionaries)

\* A bank is non-empty if there is at least one person left on it.
BankNonEmpty == \E b \in Banks : shore[b] # {}

Init ==
  /\ boatBank = "east"
  /\ shore = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ carrying = {}
  /\ crossing = FALSE

\* Passengers board the boat; this is the only way carrying becomes non-empty.
Board(p) ==
  /\ crossing = FALSE
  /\ NoEmptyCarry
  /\ p \subseteq shore[boatBank]
  /\ Cardinality(carrying) = 0
  /\ carrying' = p
  /\ crossing' = TRUE
  /\ UNCHANGED <<boatBank, shore>>

\* The boat reaches the far bank and drops its passengers.
Disembark ==
  /\ crossing = TRUE
  /\ /\ shore' = [shore EXCEPT ![boatBank] = @ \ p, ![boatBank \in {"east", "west"} ? "west" : "east"] = @ \cup p]
     /\ boatBank' = boatBank \in {"east", "west"} ? "west" : "east"
  /\ carrying' = {}
  /\ crossing' = FALSE

\* A bank that is already empty refuses to load, so disembarkation always makes
\* progress towards the next loading.
Load ==
  /\ crossing = FALSE
  /\ NoEmptyCarry
  /\ Cardinality(shore[boatBank] \ carrying) > 0
  /\ crossing' = TRUE
  /\ UNCHANGED <<boatBank, shore, carrying>>

Move ==
  \/ \E p \in SUBSET People : Board(p)
  \/ Disembark
  \/ Load

Next == Move

Spec == Init /\ [][Next]_vars

Solution == BankNonEmpty /\ \A b \in Banks : BankSafe(b)

====