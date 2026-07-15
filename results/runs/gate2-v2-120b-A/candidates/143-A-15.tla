---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

\* -------------------------------------------------
\* Constants (the two sets of participants)
\* -------------------------------------------------
CONSTANTS Missionaries, Cannibals

\* -------------------------------------------------
\* Derived constant: the set of all participants
\* -------------------------------------------------
People == Missionaries \cup Cannibals

\* -------------------------------------------------
\* State variables
\* -------------------------------------------------
VARIABLES boat, left

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
\* The opposite bank of a given bank
Opposite == [b \in {"East","West"} |-> IF b = "East" THEN "West" ELSE "East"]

\* The set of people on the other bank
Right == People \ left

\* Count of missionaries on a given set of people
MissionariesIn(S) == Cardinality(S \cap Missionaries)

\* Count of cannibals on a given set of people
CannibalsIn(S) == Cardinality(S \cap Cannibals)

\* Safety predicate for a given bank (set of people)
BankSafe(S) ==
    /\ MissionariesIn(S) = 0
       \/ CannibalsIn(S) <= MissionariesIn(S)

\* Global safety (both banks)
Safe == /\ BankSafe(left)
         /\ BankSafe(Right)

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
    /\ boat = "East"
    /\ left = Missionaries \cup Cannibals
    /\ Safe

\* -------------------------------------------------
\* Deterministic selection of one or two people from a set
\* -------------------------------------------------
SubsetsOfSizeOneOrTwo(S) ==
    { t \in SUBSET S : Cardinality(t) \in 1..2 }

\* -------------------------------------------------
\* Move action (the only possible transition)
\* -------------------------------------------------
Move ==
    \E persons \in SubsetsOfSizeOneOrTwo(
            IF boat = "East" THEN left ELSE Right) :
        /\ IF boat = "East"
              THEN /\ left' = left \ persons
                    /\ boat' = "West"
              ELSE /\ left' = left \cup persons
                    /\ boat' = "East"
        /\ Safe

\* -------------------------------------------------
\* Next-state relation
\* -------------------------------------------------
Next == Move

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<boat, left>>

\* -------------------------------------------------
\* Type correctness invariant (optional but useful)
\* -------------------------------------------------
TypeOK ==
    /\ boat \in {"East", "West"}
    /\ left \subseteq People
    /\ Safe

\* -------------------------------------------------
\* Safety invariant required by the .cfg
\* -------------------------------------------------
Solution == Safe

\* -------------------------------------------------
\* Theorems (optional, for readability)
\* -------------------------------------------------
THEOREM Spec => []Solution

====