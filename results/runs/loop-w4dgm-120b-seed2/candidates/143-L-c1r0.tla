---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, onBank

vars == <<boatAt, onBank>>

RECURSIVE Count(_, _)
Count(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN (IF f[x] THEN 1 ELSE 0) + Count(f, S \ {x})

MissionaryCount(b) == Count([p \in People |-> p \in Missionaries], onBank[b])
CannibalCount(b) == Count([p \in People |-> p \in Cannibals], onBank[b])

TypeOK ==
  /\ boatAt \in Banks
  /\ onBank \in [Banks -> SUBSET People]

Init ==
  /\ boatAt = "east"
  /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move(p, q) ==
  /\ p # q
  /\ p \in onBank[boatAt]
  /\ q \in onBank[boatAt]
  /\ Cardinality(onBank[boatAt]) >= 2
  /\ LET newEast == onBank["east"] \ {p, q} \cup (IF boatAt = "west" THEN {p, q} ELSE {})
         newWest == onBank["west"] \ {p, q} \cup (IF boatAt = "east" THEN {p, q} ELSE {})
         dest == IF boatAt = "east" THEN "west" ELSE "east"
     IN /\ (MissionaryCount("east") = 0 \/ CannibalCount("east") <= MissionaryCount("east"))
        /\ (MissionaryCount("west") = 0 \/ CannibalCount("west") <= MissionaryCount("west"))
        /\ onBank' = [b \in Banks |-> IF b = "east" THEN newEast ELSE newWest]
        /\ boatAt' = dest

Next == \E p \in People, q \in People : Move(p, q)

Solution == Cardinality(onBank["east"]) = 0

TypeOKInv == TypeOK

====