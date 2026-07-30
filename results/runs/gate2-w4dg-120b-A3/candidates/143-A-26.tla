---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals
\* EastBank and WestBank describe who is standing on each river bank.  Boat
\* records where the boat is currently docked; Loaded records who is currently
\* on board during a crossing.
VARIABLES EastBank, WestBank, Boat, Loaded

People == Missionaries \cup Cannibals

TypeOK ==
    /\ EastBank \subseteq People
    /\ WestBank \subseteq People
    /\ Boat \in {"east", "west"}
    /\ Loaded \subseteq People

\* A bank is safe when its missionaries are never outnumbered by cannibals.
\* The trivial case (no missionaries present) counts as safe.
BankSafe(S) ==
    \/ (Missionaries \cap S = {})
    \/ Cardinality(Cannibals \cap S) <= Cardinality(Missionaries \cap S)

Init ==
    /\ EastBank = People
    /\ WestBank = {}
    /\ Boat = "east"
    /\ Loaded = {}

\* Boarding loads one or two people from the current bank onto the boat; it
\* is only permitted when the distribution after the move remains safe on both
\* banks, since the move is committed atomically (no half-move state).
Board(S) ==
    /\ S \subseteq (IF Boat = "east" THEN EastBank ELSE WestBank)
    /\ Cardinality(S) \in 1..2
    /\ BankSafe((IF Boat = "east" THEN EastBank ELSE WestBank) \ S)
    /\ BankSafe((IF Boat = "east" THEN WestBank ELSE EastBank) \cup S)
    /\ EastBank' = IF Boat = "east" THEN EastBank \ S ELSE EastBank
    /\ WestBank' = IF Boat = "west" THEN WestBank \ S ELSE WestBank
    /\ Loaded' = S
    /\ UNCHANGED Boat

Disembark ==
    /\ Loaded # {}
    /\ EastBank' = IF Boat = "east" THEN EastBank ELSE EastBank \cup Loaded
    /\ WestBank' = IF Boat = "west" THEN WestBank ELSE WestBank \cup Loaded
    /\ Loaded' = {}
    /\ Boat' = IF Boat = "east" THEN "west" ELSE "east"

Next == Board({}) \/ Disembark

Solution ==
    /\ EastBank = {}
    /\ WestBank = People
    /\ Loaded = {}
    /\ Boat \in {"east", "west"}

Spec == Init /\ [][Next]_<<EastBank, WestBank, Boat, Loaded>>

====