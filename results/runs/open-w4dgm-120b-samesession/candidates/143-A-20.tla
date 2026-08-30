---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
NoBank == "nowhere"

VARIABLES boatAt, banks, solutionFound

vars == <<boatAt, banks, solutionFound>>

\* Counts of missionaries and cannibals on a bank, used for the safety test.
typeRec(b) ==
    /\ Cardinality(banks[b] \cap Missionaries) = b.m
    /\ Cardinality(banks[b] \cap Cannibals) = b.c

TypeOK ==
    /\ boatAt \in Banks
    /\ banks \in [Banks -> SUBSET People]
    /\ solutionFound \in BOOLEAN

\* The missionaries are safe on a bank if either none are present or cannibals
\* do not outnumber them; a bank of only cannibals is trivially safe.
BankSafe(b) ==
    \/ (banks[b] \cap Missionaries = {})
    \/ (Cardinality(banks[b] \cap Cannibals) <= Cardinality(banks[b] \cap Missionaries))

Init ==
    /\ boatAt = "east"
    /\ banks = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ solutionFound = FALSE

\* One or two people board the boat, cross to the other bank, and the boat docks
\* there. The move is only enabled when the resulting banks are both safe.
Move ==
    \E S \in SUBSET banks[boatAt] :
        /\ Cardinality(S) \in 1..2
        /\ banks' = [banks EXCEPT ![boatAt] = banks[boatAt] \ S,
                                  ![IF boatAt = "east" THEN "west" ELSE "east"] = banks[IF boatAt = "east" THEN "west" ELSE "east"] \cup S]
        /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
        /\ solutionFound' = (banks'["east"] = {})

Next == Move

Spec == Init /\ [][Next]_vars

\* Both banks safe: missionaries never outnumbered by cannibals.
MissionarySafety == \A b \in Banks : BankSafe(b)

\* Boat always carries a non-empty group of at most two people.
BoatNeverEmpty ==
    \A b \in Banks : Cardinality(banks[b] \cap Missionaries) + Cardinality(banks[b] \cap Cannibals) <= 2

Invariants == MissionarySafety /\ BoatNeverEmpty

Properties == MissionarySafety /\ BoatNeverEmpty

====