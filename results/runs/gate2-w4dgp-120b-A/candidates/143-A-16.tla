---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

ASSUME Missionaries # {} /\ Cannibals # {} /\ Missionaries # Cannibals

Banks == {"east", "west"}

People == Missionaries \cup Cannibals

VARIABLES boat, bank

vars == <<boat, bank>>

RECURSIVE Count(_, _)
Count(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN (IF f[x] THEN 1 ELSE 0) + Count(f, S \ {x})

TypeOK ==
    /\ boat \in Banks
    /\ bank \in [Banks -> SUBSET People]

Init ==
    /\ boat = "east"
    /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* Move a group of one or two people across the river, but only when the
\* resulting configuration on both banks is safe (missionaries are never
\* outnumbered where they are present).
Move(grp) ==
    /\ grp # {}
    /\ Cardinality(grp) <= 2
    /\ grp \subseteq bank[boat]
    /\ LET dst == IF boat = "east" THEN "west" ELSE "east"
           newbank == [bank EXCEPT ![boat] = bank[boat] \ grp, ![dst] = bank[dst] \cup grp]
       IN /\ (bank[dst] \cup grp) # {}
          /\ (Cardinality(bank[dst] \cup grp) > 0 => Count(Cannibals, bank[dst] \cup grp) <= Count(Missionaries, bank[dst] \cup grp))
          /\ (Cardinality(newbank["west"]) > 0 => Count(Cannibals, newbank["west"]) <= Count(Missionaries, newbank["west"]))
          /\ (Cardinality(newbank["east"]) > 0 => Count(Cannibals, newbank["east"]) <= Count(Missionaries, newbank["east"]))
          /\ boat' = dst
          /\ bank' = newbank

Next == \E grp \in SUBSET People : Move(grp)

\* Every reachable state is safe and carries a non-empty load on every crossing.
Solution ==
    /\ (bank["west"] # {} => Count(Cannibals, bank["west"]) <= Count(Missionaries, bank["west"]))
    /\ (bank["east"] # {} => Count(Cannibals, bank["east"]) <= Count(Missionaries, bank["east"]))

Spec == Init /\ [][Next]_vars

====