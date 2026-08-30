---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}
NONE == "none"
MaxBoat == 2

VARIABLES boatAt, peopleOn, crossing

vars == <<boatAt, peopleOn, crossing>>

\* The count of cannibals must never exceed the count of missionaries
\* on a bank that has missionaries, since that is when the missionaries
\* would be eaten.
BankSafe(b) ==
  IF peopleOn[b] \cap Missionaries = {} THEN TRUE
  ELSE Cardinality(peopleOn[b] \cap Cannibals) <= Cardinality(peopleOn[b] \cap Missionaries)

TypeOK ==
  /\ boatAt \in Banks
  /\ peopleOn \in [Banks -> SUBSET People]
  /\ crossing \in 0..MaxBoat

Init ==
  /\ boatAt = "east"
  /\ peopleOn = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ crossing = 0

\* A non-empty group of size at most the boat's capacity boards on the
\* current bank and lands on the other one; the move only fires if both
\* banks remain safe afterwards.
Move(g) ==
  /\ g \subseteq People
  /\ Cardinality(g) \in 1..MaxBoat
  /\ g \subseteq peopleOn[boatAt]
  /\ LET other == IF boatAt = "east" THEN "west" ELSE "east" IN
       /\ \A b \in Banks : Cardinality((IF b = other THEN peopleOn[b] \cup g ELSE peopleOn[b] \ g) \cap Cannibals)
                            <= Cardinality((IF b = other THEN peopleOn[b] \cup g ELSE peopleOn[b] \ g) \cap Missionaries)
       /\ peopleOn' = [b \in Banks |-> IF b = other THEN peopleOn[b] \cup g ELSE peopleOn[b] \ g]
       /\ boatAt' = other
  /\ crossing' = Cardinality(g)

Next == \E g \in SUBSET People : Move(g)

\* A solution must reach the state where the east bank is empty (every
\* person has crossed) and the boat sits on the far shore.
Solution ==
  /\ peopleOn["east"] = {}
  /\ boatAt = "west"

Spec == Init /\ [][Next]_vars
====