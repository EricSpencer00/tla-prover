---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

\* ------------------------------------------------------------
\* Derived constants
\* ------------------------------------------------------------
Banks == {"East", "West"}
People == Missionaries \cup Cannibals

\* ------------------------------------------------------------
\* State variables
\* ------------------------------------------------------------
VARIABLES Boat, BankPeople

\* Boat : the bank where the boat currently resides  ("East" or "West")
\* BankPeople : a function mapping each bank to the set of people currently on that bank

\* ------------------------------------------------------------
\* Helper definitions
\* ------------------------------------------------------------

IsSafe(bank) ==
    LET M == Missionaries \cap BankPeople[bank]
        C == Cannibals \cap BankPeople[bank]
    IN  (Cardinality(M) = 0) \/ (Cardinality(C) <= Cardinality(M))

\* A state is safe if every bank satisfies the safety condition
SafeState(S) ==
    \A b \in Banks : IsSafe(b)

\* The set of all possible groups that can board the boat (one or two people)
PossibleGroups ==
    { g \in Subsets(People, 1) \cup Subsets(People, 2) }

\* ------------------------------------------------------------
\* Initialization
\* ------------------------------------------------------------
Init ==
    /\ Boat = "East"
    /\ BankPeople = [b \in Banks |-> IF b = "East" THEN People ELSE {}]
    /\ SafeState(BankPeople)

\* ------------------------------------------------------------
\* Next action (Move)
\* ------------------------------------------------------------
Move ==
    \E g \in PossibleGroups :
        /\ g \subseteq BankPeople[Boat]                   \* group must be on current bank
        /\ Boat' = IF Boat = "East" THEN "West" ELSE "East"   \* boat moves to opposite bank
        /\ BankPeople' =
              [b \in Banks |
                  IF b = Boat THEN BankPeople[b] \ g
                 ELSE IF b = Boat' THEN BankPeople[b] \cup g
                 ELSE BankPeople[b]]
        /\ SafeState(BankPeople')                         \* safety after move

Next == Move

\* ------------------------------------------------------------
\* Type correctness (for TLC)
\* ------------------------------------------------------------
TypeOK ==
    /\ Boat \in Banks
    /\ BankPeople \in [Banks -> [People -> BOOLEAN]]
    /\ \A b \in Banks : \A p \in People : BankPeople[b][p] \in BOOLEAN

\* ------------------------------------------------------------
\* Solution invariant (the puzzle is solved when east bank is empty)
\* ------------------------------------------------------------
Solution ==
    BankPeople["East"] = {}

\* ------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------
Spec == Init /\ [][Next]_<<Boat, BankPeople>>

====