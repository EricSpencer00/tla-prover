---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}

VARIABLES boatBank, onBank
vars == <<boatBank, onBank>>

TypeOK ==
  /\ boatBank \in Banks
  /\ onBank \in [Banks -> SUBSET People]

Occupants(b) == onBank[b]
Load(b) == Cardinality(onBank[b])
MissionaryLoad(b) == Cardinality(onBank[b] \cap Missionaries)
CannibalLoad(b) == Cardinality(onBank[b] \cap Cannibals)

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
BankSafe(b) == (MissionaryLoad(b) = 0) \/ (CannibalLoad(b) <= MissionaryLoad(b))

Init ==
  /\ boatBank = "east"
  /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* Everyone on the current bank, now off the boat, and at least one person aboard.
BoardTrip ==
  [b \in Banks |-> onBank[b] \ {x \in People : x \in onBank[boatBank]}]

\* The reverse of BoardTrip: a non-empty group of one or two people disembarks.
Disembark ==
  [b \in Banks |-> onBank[b] \cup (SELECT S \in SUBSET People :
                                   /\ S \subseteq onBank["west"]
                                   /\ Cardinality(S) \in 1..2)]

Moves ==
  {Move == [boatBank |-> IF boatBank = "east" THEN "west" ELSE "east",
            onBank |-> Disembark] : BankSafe("east") /\ BankSafe("west")}

Next ==
  \/ Moves
  \/ [boatBank |-> boatBank, onBank |-> BoardTrip]

\* Every bank safe and the east bank eventually emptied: a solved crossing.
Solution ==
  /\ \A b \in Banks : BankSafe(b)
  /\ \A x \in People : x \in onBank["west"]
====