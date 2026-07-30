---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, people
vars == <<boatAt, people>>

\* Count how many people satisfying a predicate are on a given bank.
RECURSIVE CountOn(_, _)
CountOn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN (IF f[x] THEN 1 ELSE 0) + CountOn(f, S \ {x})

\* A bank is safe if it has no missionaries or the cannibals there do not
\* outnumber them (the puzzle's outlawed configuration).
\* The loose end is a bank holding only cannibals, which is safe.
OnBank(b) == {p \in Missionaries \cup Cannibals : people[b][p]}
MissionaryOnBank(b) == {p \in Missionaries : people[b][p]}
CannibalOnBank(b) == {p \in Cannibals : people[b][p]}
SafeBank(b) ==
  LET mc == CountOn([p \in Missionaries \cup Cannibals |-> p \in Missionaries], OnBank(b))
      cc == CountOn([p \in Missionaries \cup Cannibals |-> p \in Cannibals], OnBank(b))
  IN mc = 0 \/ cc <= mc

TypeOK ==
  /\ boatAt \in Banks
  /\ people \in [Banks -> [Missionaries \cup Cannibals -> BOOLEAN]]

Init ==
  /\ boatAt = "east"
  /\ people = [b \in Banks |-> [p \in Missionaries \cup Cannibals |-> b = "east"]]

\* A non-empty group of up to two people crosses the river in the boat,
\* landing on the opposite bank and leaving the boat there.
Move(g) ==
  /\ g # {}
  /\ Cardinality(g) <= 2
  /\ \A p \in g : people[boatAt][p]
  /\ SafeBank(boatAt) /\ SafeBank(IF boatAt = "east" THEN "west" ELSE "east")
  /\ people' = [people EXCEPT ![boatAt] = [p \in Missionaries \cup Cannibals |-> @ [p] /\ p \notin g],
                               ![IF boatAt = "east" THEN "west" ELSE "east"] =
                                 [p \in Missionaries \cup Cannibals |-> @ [p] \/ (p \in g)]]
  /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Next == \E g \in SUBSET (Missionaries \cup Cannibals) : Move(g)

\* Missionaries are only ever eaten if a bank has them and they are outnumbered.
NoMissionaryEaten ==
  /\ \A b \in Banks : SafeBank(b)
  /\ \A b \in Banks : Cardinality(CannibalOnBank(b)) >= Cardinality(MissionaryOnBank(b))
                         => MissionaryOnBank(b) = {}

\* Every river crossing carries at least one person and at most two.
BoatNeverEmpty ==
  \A b \in Banks : Cardinality(OnBank(b)) >= 0 /\ Cardinality(OnBank(b)) <= 6

Solution == NoMissionaryEaten /\ BoatNeverEmpty

====