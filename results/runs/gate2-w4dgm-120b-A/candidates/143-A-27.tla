---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

\* PeopleOn[b] = who is at bank b; BoatAt = the bank the boat is docked at.
VARIABLES BoatAt, PeopleOn

TypeOK ==
  /\ BoatAt \in Banks
  /\ PeopleOn \in [Banks -> SUBSET People]

Init ==
  /\ BoatAt = "east"
  /\ PeopleOn = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A crossing is safe only if both banks, after the move, still cohabit peacefully.
SafeDistribution(dist) ==
  \A b \in Banks :
    LET ms == Missionaries \cap dist[b]
        cs == Cannibals \cap dist[b]
    IN (ms = {}) \/ (Cardinality(cs) <= Cardinality(ms))

\* The boat never travels empty and never carries more than two.
Move(e1, e2) ==
  /\ e1 # e2
  /\ {e1, e2} \subseteq PeopleOn[BoatAt]
  /\ LET fromBank == BoatAt
         toBank   == CHOOSE x \in Banks : x # fromBank
         newFrom  == PeopleOn[fromBank] \ {e1, e2}
         newTo    == PeopleOn[toBank] \cup {e1, e2}
     IN /\ SafeDistribution([PeopleOn EXCEPT ![fromBank] = newFrom, ![toBank] = newTo])
        /\ BoatAt' = toBank
        /\ PeopleOn' = [PeopleOn EXCEPT ![fromBank] = newFrom, ![toBank] = newTo]

Next == \E e1 \in People : \E e2 \in People : Move(e1, e2)

Spec == Init /\ [][Next]_<<BoatAt, PeopleOn>>

\* No missionaries are ever outnumbered by cannibals on either bank.
Solution == \A b \in Banks : SafeDistribution(PeopleOn[b])

TypeOKInv == TypeOK
====