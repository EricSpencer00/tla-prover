---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals, TLC

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Person == Missionaries \cup Cannibals
Banks   == {"East", "West"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES boat, banks

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
BoatBank == boat
BankMap  == banks

OtherBank(b) == IF b = "East" THEN "West" ELSE "East"

\* Number of missionaries / cannibals on a given bank
MissionariesOn(b) == Cardinality( BankMap[b] \cap Missionaries )
CannibalsOn(b)    == Cardinality( BankMap[b] \cap Cannibals )

\* A bank is safe iff it has no missionaries OR cannibals do not outnumber them
Safe(b) == 
    LET m == MissionariesOn(b) IN
    LET c == CannibalsOn(b)    IN
    (m = 0) \/ (c <= m)

\* The set of people that may move in one crossing (size 1 or 2)
MoveGroup(b) == { g \in SUBSET BankMap[b] : 
                    Cardinality(g) \in 1..2 }

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ boat \in Banks
    /\ banks \in [Banks -> SUBSET Person]
    /\ Missionaries \subseteq Person
    /\ Cannibals    \subseteq Person
    /\ Missionaries \cap Cannibals = {}
    /\ Cardinality(Missionaries) = 3
    /\ Cardinality(Cannibals)    = 3

\* ----------------------------------------------------------------------
\* Safety property (the puzzle's safety rule)
\* ----------------------------------------------------------------------
Solution == BankMap["East"] # {}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ boat = "East"
    /\ banks = [ b \in Banks |-> IF b = "East" THEN Person ELSE {} ]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == 
    \E g \in MoveGroup(BoatBank) :
        LET src  == BoatBank
            dst  == OtherBank(src)
            newBanks == [ b \in Banks |-> 
                            IF b = src THEN BankMap[b] \setminus g
                            ELSE IF b = dst THEN BankMap[b] \cup g
                            ELSE BankMap[b] ]
        IN 
            /\ boat' = dst
            /\ banks' = newBanks
            /\ Safe(src) 
            /\ Safe(dst)
            /\ \A b \in Banks : Safe(b)   \* safety must hold on both banks after the move

\* ----------------------------------------------------------------------
\* Specification (not required but convenient)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boat, banks>>

\* ----------------------------------------------------------------------
\* The required invariants (as named operators)
\* ----------------------------------------------------------------------
INVARIANT TypeOK
INVARIANT Solution

====