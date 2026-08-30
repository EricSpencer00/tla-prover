---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

\* Banks[b] = the set of people standing on bank b; BoatAt = the bank the boat
\* is docked at. Every crossing is a Move of 1 or 2 people from the docked
\* bank to the other one, enabled only if the resulting bank populations stay
\* safe (no missionaries outnumbered by cannibals on either bank).
VARIABLES Banks, BoatAt

TypeOK ==
  /\ Banks \in [Banks -> SUBSET People]
  /\ BoatAt \in Banks

Init ==
  /\ Banks = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ BoatAt = "east"

\* A bank is safe if it has no missionaries, or its cannibals are not more
\* numerous than its missionaries.
Safe(b) ==
  LET M == Missionaries \cap Banks[b]
      C == Cannibals \cap Banks[b]
  IN M = {} \/ Cardinality(C) <= Cardinality(M)

Successors == IF BoatAt = "east" THEN "west" ELSE "east"

Move == \E G \in SUBSET People :
  /\ Cardinality(G) \in 1..2
  /\ G \subseteq Banks[BoatAt]
  /\ Safe(BoatAt \ G)
  /\ Safe(Successors \ G)
  /\ Banks' = [Banks EXCEPT ![BoatAt] = @ \ G, ![Successors] = @ \cup G]
  /\ BoatAt' = Successors

Next == Move

Spec == Init /\ [][Next]_<<Banks, BoatAt>>

\* Safety: no bank ever leaves missionaries outnumbered by cannibals, and
\* every crossing carries at least one and at most two people.
TypeOK ==
  /\ Banks \in [Banks -> SUBSET People]
  /\ BoatAt \in Banks
  /\ \A b \in Banks : Safe(b)

Solution == \A b \in Banks : Banks[b] # {}

====