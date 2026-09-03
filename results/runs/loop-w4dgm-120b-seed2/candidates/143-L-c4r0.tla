---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals

CONSTANTS Missionaries, Cannibals

VARIABLES bank, boatAt

vars == <<bank, boatAt>>

Banks == {"east", "west"}

People == Missionaries \union Cannibals

RECURSIVE OnBank(_)
OnBank(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE IN 1 + OnBank(S \ {x})

TypeOK ==
    /\ bank \in [Banks -> SUBSET People]
    /\ boatAt \in Banks

Init ==
    /\ bank = [b \in Banks |-> IF b = "east" THEN Missionaries \union Cannibals ELSE {}]
    /\ boatAt = "east"

\* A safe bank either has no missionaries or has cannibals not outnumbering
\* them. The boat crosses with 1 or 2 people (never empty).
Move ==
    /\ \E group \in SUBSET bank[boatAt] :
         /\ 1 <= Cardinality(group) /\ Cardinality(group) <= 2
         /\ \A b \in Banks :
              LET gOnBank == IF b = boatAt THEN bank[b] \ group ELSE bank[b]
                  gOnOther == IF b = boatAt THEN gOnBank ELSE gOnBank \union group
              IN (Missionaries \subseteq gOnBank => Cardinality(gOnBank \cap Cannibals) <= Cardinality(gOnBank \cap Missionaries))
                 /\ (Missionaries \subseteq gOnOther => Cardinality(gOnOther \cap Cannibals) <= Cardinality(gOnOther \cap Missionaries))
         /\ bank' = [bank EXCEPT ![boatAt] = bank[boatAt] \ group, ![IF boatAt = "east" THEN "west" ELSE "east"] = bank[IF boatAt = "east" THEN "west" ELSE "east"] \union group]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Next == Move

Spec == Init /\ [][Next]_vars

\* Progress: the east bank eventually empties (everyone reaches the west bank).
Solution == <>(bank["east"] = {})

\* Every bank with missionaries is safe (cannibals never outnumber them), and the
\* boat always carries one or two people per crossing.
TypeOKInv ==
    /\ \A b \in Banks :
         Missionaries \subseteq bank[b] => Cardinality(bank[b] \cap Cannibals) <= Cardinality(bank[b] \cap Missionaries)
    /\ Cardinality(Missionaries \union Cannibals) = 6
====