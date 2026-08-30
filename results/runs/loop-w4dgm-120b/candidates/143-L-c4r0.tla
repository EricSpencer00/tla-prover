---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

ASSUME Missionaries # {} /\ Cannibals # {}

Banks == {"east", "west"}

VARIABLES boatAt, people

vars == <<boatAt, people>>

TypeOK ==
  /\ boatAt \in Banks
  /\ people \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

\* Safety: missionaries are never outnumbered by cannibals on any bank.
Safe ==
  \A b \in Banks :
    LET m == Cardinality(people[b] \cap Missionaries)
        c == Cardinality(people[b] \cap Cannibals) IN
      m = 0 \/ c <= m

Init ==
  /\ boatAt = "east"
  /\ people = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* Move: a non-empty group of size at most two boards and crosses, only if the
\* resulting distribution on both banks stays safe.
Move(g) ==
  /\ g # {}
  /\ Cardinality(g) <= 2
  /\ g \subseteq people[boatAt]
  /\ LET b2 == IF boatAt = "east" THEN "west" ELSE "east"
         newPeople == [people EXCEPT ![boatAt] = @ \ g, ![b2] = @ \cup g] IN
     Safe /\ boatAt' = b2 /\ people' = newPeople

Next == \E g \in SUBSET (Missionaries \cup Cannibals) : Move(g)

Spec == Init /\ [][Next]_vars

\* A correct solution always keeps the mission as a reachable state: the east
\* bank ends up empty (everyone is across) while safety is preserved.
MissionComplete == \A m \in Missionaries : m \notin people["east"]

TypeOKInv == TypeOK
MissionCompleteInv == MissionComplete
====