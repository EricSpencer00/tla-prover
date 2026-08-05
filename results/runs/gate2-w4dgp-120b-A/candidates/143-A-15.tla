---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Bank == {"east", "west"}
People == Missionaries \cup Cannibals

\* The boat carries nobody unless it is moving, and a move always
\* takes at least one person and at most two.
VARIABLES dock, peoples, moving

vars == <<dock, peoples, moving>>

\* A bank is safe if it has no missionaries (nothing to eat) or the
\* missionaries are not outnumbered by cannibals.
BankSafe(g) ==
  LET ms == {p \in peoples[g] : p \in Missionaries}
      cs == {p \in peoples[g] : p \in Cannibals}
  IN ms = {} \/ Cardinality(cs) <= Cardinality(ms)

TypeOK ==
  /\ dock \in Bank
  /\ peoples \in [Bank -> SUBSET People]
  /\ moving \subseteq People

Init ==
  /\ dock = "east"
  /\ peoples = [g \in Bank |-> IF g = "east" THEN People ELSE {}]
  /\ moving = {}

\* A crossing moves a group of size 1 or 2 from the current bank to
\* the other bank.  It is guarded by safety on both banks after the move.
Move(g, grp) ==
  /\ dock = g
  /\ grp \subseteq peoples[g]
  /\ grp # {}
  /\ Cardinality(grp) <= 2
  /\ Cardinality(grp) >= 1
  /\ LET h == IF g = "east" THEN "west" ELSE "east"
         newEast == IF g = "east" THEN peoples[g] \ grp ELSE peoples[h] \cup grp
         newWest == IF g = "west" THEN peoples[g] \ grp ELSE peoples[h] \cup grp
     IN /\ BankSafe(newEast) /\ BankSafe(newWest)
     /\ peoples' = [east |-> newEast, west |-> newWest]
  /\ dock' = (IF g = "east" THEN "west" ELSE "east")
  /\ UNCHANGED moving

Next ==
  \/ \E g \in Bank, grp \in SUBSET People : Move(g, grp)

Spec == Init /\ [][Next]_vars

\* The solution is found when nothing is left on the east bank.
Solution == \A g \in Bank : peoples[g] # {} => g = "west"

====