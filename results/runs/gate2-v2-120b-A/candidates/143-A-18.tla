---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals
Banks  == {"East", "West"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES boat, people

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of people on the east bank
EastBank == people["East"]
\* The set of people on the west bank
WestBank == people["West"]

\* Type of a state (used for the TypeOK invariant)
StateType == 
    /\ boat \in Banks
    /\ people \in [Banks -> SUBSET People]
    /\ people["East"] \cup people["West"] = People
    /\ people["East"] \cap people["West"] = {}

\* Safety condition for a single bank
\* A bank is safe if it contains no missionaries,
\* or the number of cannibals does not exceed the number of missionaries.
BankSafe(bank) ==
    LET
        M == Missionaries \cap people[bank]
        C == Cannibals \cap people[bank]
    IN
        (M = {}) \/ (Cardinality(C) <= Cardinality(M))

\* The overall safety condition (both banks safe)
Safety == /\ BankSafe("East")
          /\ BankSafe("West")

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ boat = "East"
    /\ people = [b \in Banks |-> 
        IF b = "East" THEN People ELSE {}]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
\* Non‑empty group of 1 or 2 distinct people on the current bank
Group == { g \in SUBSET People :
            /\ 1 <= Cardinality(g) /\ Cardinality(g) <= 2
            /\ g \subseteq (IF boat = "East" THEN people["East"] ELSE people["West"]) }

\* Destination bank
DestBank == IF boat = "East" THEN "West" ELSE "East"

\* Move action: a group boards, crosses, and disembarks
Move ==
    \E g \in Group :
        /\ boat' = DestBank
        /\ people' = [
                "East" |-> IF boat = "East"
                            THEN people["East"] \ g
                            ELSE people["East"] \cup g,
                "West" |-> IF boat = "West"
                            THEN people["West"] \ g
                            ELSE people["West"] \cup g
            ]
        /\ Safety

Next == Move

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Type correctness (helps TLC catch mis‑typed states)
TypeOK == StateType

\* The solution condition: eventually everybody is on the west bank.
\* (The invariant itself states the goal state; a liveness property would
\*  assert that it is eventually reached, but only the invariant is required.)
Solution == people["East"] = {}

\* ----------------------------------------------------------------------
\* The specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boat, people>>

\* ----------------------------------------------------------------------
\* Theorems (optional, but useful for documentation)
\* ----------------------------------------------------------------------
THEOREM Spec => []Safety

=============================================================================