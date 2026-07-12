---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Banks == {"East", "West"}
People == Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Boat, On

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
BoatAt(b) == Boat = b

\* The set of people on a given bank
BankPeople(b) == On[b]

\* Safety predicate for a single bank
SafeBank(b) ==
    \E m \in Missionaries :
        (m \in BankPeople(b)) => (Cardinality(Cannibals \cap BankPeople(b)) <= Cardinality(Missionaries \cap BankPeople(b)))
    \* If no missionaries on the bank, the condition is vacuously true

\* Overall safety condition
Safe == SafeBank("East") /\ SafeBank("West")

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Boat = "East"
    /\ On = [b \in Banks |-> IF b = "East" THEN People ELSE {}]
    /\ Safe

\* ----------------------------------------------------------------------
\* Move action
\* ----------------------------------------------------------------------
Move ==
    \E group \in Subset(People) :
        /\ Cardinality(group) \in {1, 2}
        /\ group \subseteq BankPeople(Boat)
        /\ \E dest \in Banks \ {Boat} :
            /\ \E newOn \in [b \in Banks |-> IF b = dest THEN BankPeople(b) \cup group
                                            ELSE IF b = Boat THEN BankPeople(b) \ group
                                            ELSE BankPeople(b)]
            /\ SafeBank(dest) /\ SafeBank(Boat)
            /\ Boat' = dest
            /\ On' = newOn

Next == Move

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Boat \in Banks
    /\ On \in [b \in Banks |-> SUBSET People]
    /\ \A b \in Banks : On[b] \subseteq People

\* ----------------------------------------------------------------------
\* Solution invariant (the puzzle is solved when the east bank is empty)
\* ----------------------------------------------------------------------
Solution ==
    On["East"] = {}

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Boat, On>>

====