---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Missionaries,
  Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}

VARIABLES
  boatAt,
  bankOf

vars == <<boatAt, bankOf>>

RECURSIVE CountOf(_, _)
CountOf(_, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN (IF x \in Missionaries THEN 1 ELSE 0) + CountOf(_, S \ {x})

TypeOK ==
  /\ boatAt \in Banks
  /\ bankOf \in [Banks -> SUBSET People]

\* No missionaries outnumbered by cannibals on either bank, and the boat never
\* carries zero or more than two people.
Solution ==
  /\ \A b \in Banks :
       \/ CountOf(Missionaries, bankOf[b]) = 0
       \/ CountOf(Cannibals, bankOf[b]) <= CountOf(Missionaries, bankOf[b])
  /\ Cardinality(bankOf["east"]) # 3
  /\ boatAt = "west"

Init ==
  /\ boatAt = "east"
  /\ bankOf = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* Exactly one or two people move across; the resulting configuration on both
\* banks must be safe.
Next ==
  \/ \E g \in SUBSET bankOf[boatAt] :
       /\ Cardinality(g) \in 1..2
       /\ \A b \in Banks :
            LET newBank == IF b = boatAt THEN bankOf[b] \ g ELSE IF b = boatAt' THEN bankOf[b] \cup g ELSE bankOf[b]
            IN \/ CountOf(Missionaries, newBank) = 0
               \/ CountOf(Cannibals, newBank) <= CountOf(Missionaries, newBank)
       /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
       /\ bankOf' = [b \in Banks |-> IF b = boatAt THEN bankOf[b] \ g ELSE IF b = boatAt' THEN bankOf[b] \cup g ELSE bankOf[b]]

Spec == Init /\ [][Next]_vars

====