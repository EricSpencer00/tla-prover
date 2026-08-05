---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank, boatAt

vars == <<bank, boatAt>>

Banks == {"east", "west"}

\* A bank is safe if it either has no missionaries, or the cannibals on it never outnumber
\* the missionaries (the missionaries are never endangered there).
Safe(b) == (Missionaries \cap bank[b] = {}) \/ (Cardinality(Cannibals \cap bank[b]) <= Cardinality(Missionaries \cap bank[b]))

TypeOK ==
  /\ bank \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
  /\ boatAt \in Banks
  /\ Missionaries \cap Cannibals = {}
  /\ Missionaries \cup Cannibals # {}

Init ==
  /\ bank = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]
  /\ boatAt = "east"

\* The boat carries one or two people across from the current bank to the other.  After the
\* crossing both banks must remain safe (nobody can be left with more cannibals than missionaries).
Move(p) ==
  /\ p \subseteq bank[boatAt]
  /\ 1 <= Cardinality(p) /\ Cardinality(p) <= 2
  /\ Safe(boatAt)
  /\ LET other == IF boatAt = "east" THEN "west" ELSE "east"
     IN /\ \A b \in Banks : Cardinality(Cannibals \cap ((IF b = boatAt THEN bank[b] \ p ELSE bank[b]) \cup (IF b = other THEN p ELSE {}))) <=
                          Cardinality(Missionaries \cap ((IF b = boatAt THEN bank[b] \ p ELSE bank[b]) \cup (IF b = other THEN p ELSE {})))
        /\ bank' = [b \in Banks |-> ((IF b = boatAt THEN bank[b] \ p ELSE bank[b]) \cup (IF b = other THEN p ELSE {}))]
        /\ boatAt' = other
  /\ UNCHANGED <<>>

Next == \E p \in SUBSET (Missionaries \cup Cannibals) : Move(p)

\* Every reachable state must have a safe crossing available, and when the puzzle is solved
\* (the source bank is empty) the boat must be standing on the destination bank.
Solution ==
  /\ \A b \in Banks : Safe(b)
  /\ (Missionaries \cup Cannibals \subseteq bank["west"]) => (boatAt = "west")

Spec == Init /\ [][Next]_vars

====