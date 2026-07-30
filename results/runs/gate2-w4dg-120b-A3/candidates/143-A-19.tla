---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
BoatCap == 2

VARIABLES
  boatDock, bankPeople

vars == <<boatDock, bankPeople>>

RECURSIVE Count(_, _)
Count(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
           rest == Count(f, S \ {x})
       IN IF f[x] THEN 1 + rest ELSE rest

TypeOK ==
  /\ boatDock \in Banks
  /\ bankPeople \in [Banks -> SUBSET People]
  /\ Cardinality(Cannibals) = 3
  /\ Cardinality(Missionaries) = 3

Init ==
  /\ boatDock = "east"
  /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

SafeBank(b) ==
  \/ bankPeople[b] \cap Missionaries = {}
  \/ Count(bankPeople[b], Cannibals) <= Count(bankPeople[b], Missionaries)

\* The group that crosses must leave both banks safe afterwards.
Move ==
  \/ \E g \in SUBSET bankPeople[boatDock] :
       /\ g # {}
       /\ Cardinality(g) <= BoatCap
       /\ LET dest == IF boatDock = "east" THEN "west" ELSE "east"
              newEast == IF dest = "east" THEN bankPeople["east"] \cup g ELSE bankPeople["east"] \ g
              newWest == IF dest = "west" THEN bankPeople["west"] \cup g ELSE bankPeople["west"] \ g
          IN /\ SafeBank(newEast)
             /\ SafeBank(newWest)
             /\ bankPeople' = [bankPeople EXCEPT ![boatDock] = newEast, ![dest] = newWest]
       /\ boatDock' = IF boatDock = "east" THEN "west" ELSE "east"
  /\ UNCHANGED <<>>

Next == Move

Spec == Init /\ [][Next]_vars

\* At least one missionary must be present for the outnumbering rule to apply.
Solution == \A b \in Banks : SafeBank(b)

====