---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES boat, eastBank, westBank

\* ----------------------------------------------------------------------
\* Type definitions (used in TypeOK invariant)
\* ----------------------------------------------------------------------
Bank == {"east", "west"}

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* People on a given bank
PeopleOn(b) == IF b = "east" THEN eastBank ELSE westBank

\* Number of missionaries on a given bank
NumMissionaries(b) == Cardinality({p \in PeopleOn(b) : p \in Missionaries})

\* Number of cannibals on a given bank
NumCannibals(b) == Cardinality({p \in PeopleOn(b) : p \in Cannibals})

\* Safety condition for a specific bank
BankSafe(b) ==
  \/ NumMissionaries(b) = 0
  \/ NumCannibals(b) <= NumMissionaries(b)

\* Overall safety (both banks)
Safe == BankSafe("east") /\ BankSafe("west")

\* The set of possible groups that can board the boat (1 or 2 people)
PossibleMoves ==
  { g \subseteq People : Cardinality(g) \in 1..2 }

\* The group of people that actually moves in a given transition
MoveGroup == VARIABLE g

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ eastBank = Missionaries \cup Cannibals
  /\ westBank = {}
  /\ boat = "east"
  /\ UNCHANGED MoveGroup

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E g \in PossibleMoves :
    /\ g \subseteq PeopleOn(boat)               \* they must be on the current bank
    /\ LET dest == IF boat = "east" THEN "west" ELSE "east" IN
       /\ IF boat = "east"
            THEN /\ eastBank' = eastBank \ g
                 /\ westBank' = westBank \cup g
            ELSE /\ westBank' = westBank \ g
                 /\ eastBank' = eastBank \cup g
       /\ boat' = dest
       /\ Safe'                                 \* safety after the move
    /\ UNCHANGED MoveGroup

\* ----------------------------------------------------------------------
\* Specification (used only for completeness, not required by cfg)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boat, eastBank, westBank>>

\* ----------------------------------------------------------------------
\* Invariant: TypeOK
\* ----------------------------------------------------------------------
TypeOK ==
  /\ boat \in Bank
  /\ eastBank \subseteq People
  /\ westBank \subseteq People
  /\ eastBank \cup westBank = People
  /\ eastBank \cap westBank = {}

\* ----------------------------------------------------------------------
\* Invariant: Solution
\* This invariant captures the safety condition and the requirement
\* that the boat never travels empty (ensured by the definition of
\* PossibleMoves).  It also asserts the liveness goal in safety form:
\* the east bank eventually becomes empty, but as an invariant we
\* simply require that the east bank is never non‑empty **and** safe.
\* The model checker will look for a violation of the negation of this
\* invariant to find a solution trace.
\* ----------------------------------------------------------------------
Solution ==
  /\ Safe
  /\ boat \in {"east", "west"}                \* boat always on a bank
  /\ IF boat = "east" THEN
        Cardinality(g) >= 1 /\ Cardinality(g) <= 2
     ELSE TRUE                                 \* the action determines the move size
  /\ eastBank = {} \/ westBank = {}

\* ----------------------------------------------------------------------
\* THEOREM: The specification implies the invariants (optional)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====