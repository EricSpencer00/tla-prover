---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals
Banks  == {"East", "West"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES bank, boatPos

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Number of missionaries and cannibals on a given bank
MissionariesOn(b) == Cardinality(bank[b] \cap Missionaries)
CannibalsOn(b)    == Cardinality(bank[b] \cap Cannibals)

\* A bank is safe if it has no missionaries or missionaries are not outnumbered
SafeBank(b) == 
    LET m == MissionariesOn(b) 
        c == CannibalsOn(b) 
    IN  m = 0 \/ c <= m

AllBanksSafe == \A b \in Banks : SafeBank(b)

\* The opposite bank of the current boat position
Opposite(b) == IF b = "East" THEN "West" ELSE "East"

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ boatPos = "East"
    /\ bank = [b \in Banks |-> IF b = "East" THEN People ELSE {}]

\* ----------------------------------------------------------------------
\* Move action: transport 1 or 2 people from the current bank to the other
\* ----------------------------------------------------------------------
Move ==
    \E grp \subseteq bank[boatPos] :
        (Cardinality(grp) = 1 \/ Cardinality(grp) = 2) /\ 
        LET newBank == [b \in Banks |-> 
                          IF b = boatPos 
                             THEN bank[b] \ grp 
                             ELSE bank[b] \cup grp] IN
        /\ boatPos' = Opposite(boatPos)
        /\ bank'    = newBank
        /\ \A b \in Banks :
               LET m == Cardinality(newBank[b] \cap Missionaries)
                   c == Cardinality(newBank[b] \cap Cannibals)
               IN m = 0 \/ c <= m

Next == Move

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ boatPos \in Banks
    /\ bank \in [Banks -> SUBSET People]
    /\ bank["East"] \cup bank["West"] = People
    /\ bank["East"] \cap bank["West"] = {}

\* ----------------------------------------------------------------------
\* Solution invariant (the east bank must remain non‑empty; violation yields a solution)
\* ----------------------------------------------------------------------
Solution == bank["East"] # {}

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<bank, boatPos>>

\* ----------------------------------------------------------------------
\* Theorems / properties (optional)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Solution

====