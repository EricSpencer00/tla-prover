---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

\* Constants representing the sets of missionaries and cannibals
CONSTANT Missionaries, Cannibals

MissionariesAndCannibals == Missionaries \cup Cannibals

\* Banks
Banks == {"East", "West"}

\* Type alias for a set of people
People == SUBSET MissionariesAndCannibals

VARIABLES boat, eastBank, westBank

\* State predicate that describes the entire state
State == 
    /\ boat \in Banks
    /\ eastBank \in SUBSET MissionariesAndCannibals
    /\ westBank \in SUBSET MissionariesAndCannibals
    /\ eastBank \cup westBank = MissionariesAndCannibals
    /\ eastBank \cap westBank = {}

\* Helper definitions
EastPeople == eastBank
WestPeople == westBank

MissionariesIn(S) == S \cap Missionaries
CannibalsIn(S)   == S \cap Cannibals

MissionariesCount(S) == Cardinality(MissionariesIn(S))
CannibalsCount(S)   == Cardinality(CannibalsIn(S))

\* Safety condition for a given bank
BankSafe(S) == 
    \/ MissionariesCount(S) = 0
    \/ CannibalsCount(S) <= MissionariesCount(S)

\* Global safety invariant
Safe == /\ BankSafe(eastBank)
        /\ BankSafe(westBank)

\* Boat must always carry 1 or 2 people (enforced by the transition relation)
BoatLoadSize == IF boat = "East" THEN MissionariesCount(eastBank) + CannibalsCount(eastBank)
                ELSE MissionariesCount(westBank) + CannibalsCount(westBank)

\* Initial state
Init ==
    /\ boat = "East"
    /\ eastBank = MissionariesAndCannibals
    /\ westBank = {}

\* A move consists of selecting a group G of size 1 or 2 from the current bank,
\* moving them to the opposite bank, and toggling the boat location.
\* The move is allowed only if both banks remain safe after the move.
Next ==
    \/ \E G \subseteq eastBank :
          /\ Cardinality(G) \in 1..2
          /\ westBank' = westBank \cup G
          /\ eastBank' = eastBank \ G
          /\ boat' = "West"
          /\ SafeAfterMove
    \/ \E G \subseteq westBank :
          /\ Cardinality(G) \in 1..2
          /\ eastBank' = eastBank \cup G
          /\ westBank' = westBank \ G
          /\ boat' = "East"
          /\ SafeAfterMove
    \/ UNCHANGED <<boat, eastBank, westBank>>

\* Safety after the move (used in both directions)
SafeAfterMove ==
    /\ BankSafe(eastBank')
    /\ BankSafe(westBank')

\* Type correctness invariant (helps TLC)
TypeOK ==
    /\ boat \in Banks
    /\ eastBank \in SUBSET MissionariesAndCannibals
    /\ westBank \in SUBSET MissionariesAndCannibals
    /\ eastBank \cup westBank = MissionariesAndCannibals

\* The puzzle is solved when the east bank is empty (all have crossed)
Solution == eastBank = {}

\* The specification
Spec == Init /\ [][Next]_<<boat, eastBank, westBank>>

\* For TLC configuration
THEOREM Spec => []Safe

====