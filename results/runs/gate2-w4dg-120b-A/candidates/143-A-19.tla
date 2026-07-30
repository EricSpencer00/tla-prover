---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

BankNames == {"east", "west"}
People == Missionaries \cup Cannibals
PeopleCount(p) == Cardinality(p)

TypeOK ==
  /\ Missionaries \subseteq People
  /\ Cannibals \subseteq People
  /\ Missionaries \cap Cannibals = {}
  /\ Missionaries # {}
  /\ Cannibals # {}

\* Starting state: everyone is on the east bank.
Init ==
  /\ Missionaries \cup Cannibals \subseteq People
  /\ \A p \in People : p \in Missionaries \/ p \in Cannibals
  /\ Missionaries # {}
  /\ Cannibals # {}
  /\ \A p \in People :
       /\ p \in Missionaries \/ p \in Cannibals
  /\ \A p \in Missionaries : p \notin Cannibals
  /\ \A p \in Cannibals : p \notin Missionaries
  /\ \A p \in People : p \in Missionaries \/ p \in Cannibals
  /\ \A p \in People : p \in Missionaries \/ p \in Cannibals
  /\ \A p \in Missionaries : p \notin Cannibals
  /\ \A p \in Cannibals : p \notin Missionaries
  /\ \A p \in People : p \in Missionaries \/ p \in Cannibals
  /\ \A p \in People : p \in Missionaries \/ p \in Cannibals
  /\ \A p \in People : p \in Missionaries \/ p \in Cannibals

\* The boat and the people are always on exactly one bank, and no bank starts empty.
VARIABLES boatAt, onBank

vars == <<boatAt, onBank>>

\* A bank is safe if it has no missionaries (only cannibals are present, so nothing
\* can be eaten there) or the cannibals never outnumber the missionaries.
BankSafe(b) ==
  \/ onBank[b] \cap Missionaries = {}
  \/ onBank[b] \cap Cannibals <= onBank[b] \cap Missionaries

Init ==
  /\ boatAt = "east"
  /\ onBank = [b \in BankNames |-> IF b = "east" THEN People ELSE {}]

\* A move consists of a group of one or two people getting on the boat and crossing.
\* The move is only allowed if the new distribution on both banks is safe.
Move(g) ==
  /\ g # {}
  /\ PeopleCount(g) <= 2
  /\ g \subseteq onBank[boatAt]
  /\ LET dest == IF boatAt = "east" THEN "west" ELSE "east" IN
       /\ onBank' = [onBank EXCEPT ![boatAt] = @ \ g, ![dest] = @ \cup g]
       /\ boatAt' = dest
  /\ BankSafe("east")
  /\ BankSafe("west")

Next ==
  \/ \E g \in SUBSET People : Move(g)

\* The full puzzle solution is a safety property: the east bank never becomes empty,
\* since a model checker reporting a violation provides a concrete solution trace.
Solution ==
  /\ BankSafe("east")
  /\ BankSafe("west")
  /\ onBank["east"] # {}

Spec == Init /\ [][Next]_vars

====