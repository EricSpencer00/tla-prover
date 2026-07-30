---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank, people
vars == <<bank, people>>

\* bank: the bank the boat is docked at; people: who is on each bank.
OnEast == Missionaries \cup Cannibals

RECURSIVE Sum(_, _)
Sum(set, f) ==
  IF set = {} THEN 0
  ELSE LET x == CHOOSE e \in set : TRUE IN f[x] + Sum(set \ {x}, f)

TypeOK ==
  /\ bank \in {"east", "west"}
  /\ people \in [bank -> SUBSET (Missionaries \cup Cannibals)]

Init ==
  /\ bank = "east"
  /\ people = [b \in bank |-> IF b = "east" THEN OnEast ELSE {}]

\* Count of missionaries/cannibals on a given bank.
MCCount(b) ==
  << Sum(people[b], [x \in Missionaries \cup Cannibals |-> IF x \in Missionaries THEN 1 ELSE 0]),
     Sum(people[b], [x \in Missionaries \cup Cannibals |-> IF x \in Cannibals THEN 1 ELSE 0]) >>

\* Safe: either no missionaries, or cannibals do not outnumber them.
BankSafe(b) ==
  LET p == MCCount(b) IN (p[1] = 0) \/ (p[2] <= p[1])

\* The boat must never travel empty and carries at most two people.
Move ==
  /\ \E group \in SUBSET people[bank] :
       /\ group # {}
       /\ Cardinality(group) <= 2
       /\ people' = [people EXCEPT ![bank] = people[bank] \ group,
                                   ![IF bank = "east" THEN "west" ELSE "east"] =
                                      people[IF bank = "east" THEN "west" ELSE "east"] \cup group]
  /\ bank' = IF bank = "east" THEN "west" ELSE "east"

Next == Move

\* The east bank becomes empty only when every person has crossed.
Solution == people["east"] = {}

Spec == Init /\ [][Next]_vars

====