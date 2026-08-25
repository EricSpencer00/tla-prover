---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals
Side   == {"East", "West"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES BoatPos, Bank

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Opposite(s) == IF s = "East" THEN "West" ELSE "East"

SafeBank(b) ==
  \/ (Cardinality(b \cap Missionaries) = 0)
  \/ (Cardinality(b \cap Cannibals) <= Cardinality(b \cap Missionaries))

AllPeopleAccounted ==
  /\ \A s \in Side : Bank[s] \subseteq People
  /\ UNION { Bank[s] : s \in Side } = People
  /\ \A s1, s2 \in Side : s1 # s2 => Bank[s1] \cap Bank[s2] = {}

\* ----------------------------------------------------------------------
\* Type correctness and safety invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ BoatPos \in Side
  /\ Bank \in [Side -> SUBSET People]
  /\ \A s \in Side : SafeBank(Bank[s])
  /\ AllPeopleAccounted

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ BoatPos = "East"
  /\ Bank = [ "East" |-> People,
              "West" |-> {} ]

\* ----------------------------------------------------------------------
\* Move action (boat carries 1 or 2 people)
\* ----------------------------------------------------------------------
Move ==
  \E moving \in SUBSET Bank[BoatPos] :
    /\ Cardinality(moving) \in 1..2
    /\ LET newPos == Opposite(BoatPos) IN
       /\ BoatPos' = newPos
       /\ Bank' = [ BoatPos    |-> (Bank[BoatPos] \ moving),
                    newPos     |-> (Bank[newPos] \cup moving) ]
    /\ \A s \in Side : SafeBank(Bank'[s])

Next == Move

\* ----------------------------------------------------------------------
\* Solution invariant (east bank must stay non‑empty; violation signals success)
\* ----------------------------------------------------------------------
Solution == Bank["East"] # {}

=============================================================================