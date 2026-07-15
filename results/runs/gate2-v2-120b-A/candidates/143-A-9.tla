---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants representing the set of missionaries and the set of cannibals.
\* Each constant is a set of distinct identifiers.  The concrete values are
\* supplied by the .cfg file.
\* ----------------------------------------------------------------------
CONSTANT Missionaries
CONSTANT Cannibals

\* ----------------------------------------------------------------------
\* Derived constant: the set of all people (missionaries ∪ cannibals).
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* Type invariant used by the model checker.
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Missionaries \subseteq People
  /\ Cannibals \subseteq People
  /\ Missionaries \cap Cannibals = {}

\* ----------------------------------------------------------------------
\* State variables.
\*   Boat   : the bank where the boat is currently docked ("East" or "West")
\*   East   : the set of people currently on the east bank
\*   West   : the set of people currently on the west bank
\* ----------------------------------------------------------------------
VARIABLES Boat, East, West

\* ----------------------------------------------------------------------
\* Helper definitions.
\* ----------------------------------------------------------------------
EastBank == "East"
WestBank == "West"

PeopleOnBank(b) == IF b = EastBank THEN East ELSE West

\* Safety condition for a single bank.
\* A bank is safe if it contains no missionaries, or the number of
\* cannibals on that bank does not exceed the number of missionaries.
\* ----------------------------------------------------------------------
SafeBank(b) ==
  LET bankSet == PeopleOnBank(b) IN
    (Missionaries \cap bankSet = {}) \/
    (Cardinality(Cannibals \cap bankSet) <= Cardinality(Missionaries \cap bankSet))

\* Global safety condition (used for invariants and action enabling).
\* ----------------------------------------------------------------------
Safe == /\ SafeBank(EastBank)
        /\ SafeBank(WestBank)

\* ----------------------------------------------------------------------
\* Initial state: everyone starts on the east bank; the boat is docked there.
\* ----------------------------------------------------------------------
Init ==
  /\ Boat = EastBank
  /\ East = People
  /\ West = {}

\* ----------------------------------------------------------------------
\* Move action: a non‑empty group of one or two people crosses the river.
\* The action is only enabled when the resulting configuration is safe.
\* ----------------------------------------------------------------------
Move ==
  \E group \in SUBSET People :
    /\ Cardinality(group) \in 1..2               \* boat carries 1 or 2 people
    /\ group \subseteq PeopleOnBank(Boat)        \* they must be on the current bank
    /\ LET newEast ==
           IF Boat = EastBank
              THEN East \ group
              ELSE East \cup group
       IN
       LET newWest ==
           IF Boat = WestBank
              THEN West \ group
              ELSE West \cup group
       IN
       /\ newEast \cup newWest = People          \* nobody disappears
       /\ newEast \cap newWest = {}               \* nobody is on both banks
       /\ Boat' = IF Boat = EastBank THEN WestBank ELSE EastBank
       /\ East' = newEast
       /\ West' = newWest
       /\ Safe'                                   \* safety after the move

\* ----------------------------------------------------------------------
\* Stuttering step to keep the model from deadlocking when no move is
\* possible (the model checker will still explore all real moves).
\* ----------------------------------------------------------------------
Stutter ==
  /\ Boat' = Boat
  /\ East' = East
  /\ West' = West

Next == Move \/ Stutter

\* ----------------------------------------------------------------------
\* Safety invariant required by the .cfg file.
\* ----------------------------------------------------------------------
Solution == Safe

\* ----------------------------------------------------------------------
\* The specification (optional, but often useful).
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Boat, East, West>>

=============================================================================