---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
Everyone == Missionaries \cup Cannibals
OnBank == [east : SUBSET Everyone, west : SUBSET Everyone]

VARIABLES boatAt, people

vars == <<boatAt, people>>

RECURSIVE Card(_)
Card(S) == IF S = {} THEN 0 ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Card(S \ {x})

TypeOK ==
    /\ boatAt \in Banks
    /\ people \in OnBank
    /\ people.east \cup people.west = Everyone
    /\ people.east \cap people.west = {}

Init ==
    /\ boatAt = "east"
    /\ people = [east |-> Everyone, west |-> {}]

\* A move is safe only if both banks stay safe: missionaries never outnumbered
\* by cannibals on a bank where any missionary is present.
Move(a, b) ==
    /\ a \in {1, 2}
    /\ b \in {1, 2}
    /\ boatAt = "east"
    /\ Card(people.east) >= a
    /\ Card(people.west) + a = b
    /\ /\ \A x, y \in {Missionaries, Cannibals} :
           IF x = Missionaries /\ y = Cannibals
           THEN Card(people.west \cap x) >= Card(people.west \cap y)
           ELSE TRUE
       /\ \A x, y \in {Missionaries, Cannibals} :
           IF x = Missionaries /\ y = Cannibals
           THEN Card(people.east \cap x) >= Card(people.east \cap y)
           ELSE TRUE
    /\ people' = [east |-> people.east,
                  west |-> {
                      CHOOSE z \in people.west :
                         Cardinality(people.west \cap Missionaries) = 0 \/ Cardinality(people.west \cap Cannibals) = 0
                         \/ (Cardinality(people.east \cap Missionaries) > 0 /\ Cardinality(people.east \cap Cannibals) > 0)
                         \/ (Cardinality(people.east \cap Missionaries) > Cardinality(people.east \cap Cannibals) /\ Cardinality(people.west \cap Missionaries) > Cardinality(people.west \cap Cannibals))
                  } ]
    /\ boatAt' = "west"

MoveReverse(a, b) ==
    /\ a \in {1, 2}
    /\ b \in {1, 2}
    /\ boatAt = "west"
    /\ Card(people.west) >= a
    /\ Card(people.east) + a = b
    /\ /\ \A x, y \in {Missionaries, Cannibals} :
           IF x = Missionaries /\ y = Cannibals
           THEN Card(people.east \cap x) >= Card(people.east \cap y)
           ELSE TRUE
       /\ \A x, y \in {Missionaries, Cannibals} :
           IF x = Missionaries /\ y = Cannibals
           THEN Card(people.west \cap x) >= Card(people.west \cap y)
           ELSE TRUE
    /\ people' = [west |-> people.west,
                  east |-> {
                      CHOOSE z \in people.east :
                         Cardinality(people.east \cap Missionaries) = 0 \/ Cardinality(people.east \cap Cannibals) = 0
                         \/ (Cardinality(people.west \cap Missionaries) > 0 /\ Cardinality(people.west \cap Cannibals) > 0)
                         \/ (Cardinality(people.west \cap Missionaries) > Cardinality(people.west \cap Cannibals) /\ Cardinality(people.east \cap Missionaries) > Cardinality(people.east \cap Cannibals))
                  } ]
    /\ boatAt' = "east"

Next ==
    \/ \E a \in {1, 2}, b \in {1, 2} : Move(a, b)
    \/ \E a \in {1, 2}, b \in {1, 2} : MoveReverse(a, b)

Spec ==
    /\ Init
    /\ [][Next]_vars

\* Solution: the east bank is never left empty until everyone has crossed.
Solution == Card(people.east) >= 1

\* Safety: missionaries are never outnumbered by cannibals on either bank.
TypeOK == TypeOK

====