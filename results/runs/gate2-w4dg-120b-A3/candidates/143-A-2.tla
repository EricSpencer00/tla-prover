---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

ASSUME Cardinality(Missionaries) = 3
ASSUME Cardinality(Cannibals) = 3

People == Missionaries \cup Cannibals

Banks == {"east", "west"}
NoBank == "nobank"

VARIABLES boatAt, bank, trips
vars == <<boatAt, bank, trips>>

RECURSIVE GroupCount(_, _)
GroupCount(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + GroupCount(f, S \ {x})

OnBank(b) == GroupCount([x \in People |-> IF bank[x] = b THEN 1 ELSE 0], People)
CannibalsOn(b) == GroupCount([x \in Cannibals |-> IF bank[x] = b THEN 1 ELSE 0], Cannibals)
MissionariesOn(b) == GroupCount([x \in Missionaries |-> IF bank[x] = b THEN 1 ELSE 0], Missionaries)

TypeOK ==
  /\ boatAt \in Banks
  /\ bank \in [People -> Banks]
  /\ trips \in 0..10

Init ==
  /\ boatAt = "east"
  /\ bank = [p \in People |-> "east"]
  /\ trips = 0

\* The move group is chosen from the bank where the boat is docked; the move is
\* only allowed if, after it, both banks still satisfy the safety rule.
Move ==
  /\ \E g \in SUBSET People :
       /\ Cardinality(g) \in {1, 2}
       /\ \A p \in g : bank[p] = boatAt
       /\ \E dest \in Banks \ {boatAt} :
            /\ \A b \in Banks :
                 LET newBank ==
                      [bank EXCEPT ![p] = IF p \in g THEN dest ELSE bank[p]]
                 IN LET nc == GroupCount([x \in Cannibals |-> IF newBank[x] = b THEN 1 ELSE 0], Cannibals)
                        nm == GroupCount([x \in Missionaries |-> IF newBank[x] = b THEN 1 ELSE 0], Missionaries)
                    IN \/ nm = 0
                       \/ nc <= nm
            /\ boatAt' = dest
       /\ bank' = [bank EXCEPT ![p] = IF p \in g THEN dest ELSE bank[p]]
  /\ trips' = IF trips < 10 THEN trips + 1 ELSE trips

Next == Move

\* Safety: missionaries are never outnumbered by cannibals on any bank.
Solution ==
  /\ \A b \in Banks :
       \/ MissionariesOn(b) = 0
       \/ CannibalsOn(b) <= MissionariesOn(b)
  /\ trips >= 1
  /\ boatAt \in Banks
  /\ bank \in [People -> Banks]

Spec == Init /\ [][Next]_vars

====