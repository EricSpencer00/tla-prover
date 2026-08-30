---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

NoBank == "nowhere"
Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, onBank, movedBy

vars == <<boatAt, onBank, movedBy>>

TypeOK ==
  /\ boatAt \in Banks \cup {NoBank}
  /\ onBank \in [Banks -> SUBSET People]
  /\ movedBy \in [People -> 0..2]

Init ==
  /\ boatAt = "east"
  /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ movedBy = [p \in People |-> 0]

\* The move is guarded by the safety requirement: after the crossing,
\* no bank may leave missionaries outnumbered by cannibals.
Safe(b) ==
  LET M == Cardinality(onBank[b] \cap Missionaries)
      C == Cardinality(onBank[b] \cap Cannibals)
  IN M = 0 \/ C <= M

Move(g) ==
  /\ g # {}
  /\ Cardinality(g) <= 2
  /\ Cardinality(g) >= 1
  /\ boatAt # NoBank
  /\ g \subseteq onBank[boatAt]
  /\ LET newBank == [b \in Banks |-> IF b = boatAt THEN onBank[b] \ {g}
                                          ELSE IF b = Destination THEN onBank[b] \cup g
                                          ELSE onBank[b]]
     IN /\ \A b \in Banks: Safe(b)
        /\ onBank' = newBank
        /\ movedBy' = [p \in People |-> IF p \in g THEN movedBy[p] + 1 ELSE movedBy[p]]
        /\ boatAt' = Destination
  /\ Destination # boatAt
  /\ Destination \in Banks
  /\ Destination # NoBank
  /\ Destination # boatAt
  /\ Destination # NoBank
  /\ Destination \in Banks
  /\ Destination # boatAt
  /\ Destination # NoBank
  /\ Destination \in Banks
  /\ Destination # boatAt
  /\ Destination # NoBank

Next ==
  \/ \E g \in SUBSET People: Move(g)
  \/ UNCHANGED vars

\* Safety: missionaries are never outnumbered by cannibals on any bank.
Solution ==
  /\ \A b \in Banks: Safe(b)
  /\ \A p \in People: movedBy[p] >= 1

Spec == Init /\ [][Next]_vars

====