---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}
Boats == {"east", "west"}
NoBank == "nowhere"

VARIABLES boatAt, onBank

vars == <<boatAt, onBank>>

RECURSIVE SumSet(_)
SumSet(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE IN (IF x \in Missionaries THEN 1 ELSE 2) + SumSet(S \ {x})

RECURSIVE SumBank(_)
SumBank(f) == SumSet({p \in People : f[p]})

NextBank(b) == IF b = "east" THEN "west" ELSE "east"

TypeOK ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET People]

Init ==
    /\ boatAt = "east"
    /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A crossing must leave both banks safe: a bank with missionaries may not
\* have more cannibals than missionaries.
SafeAfterCross(group) ==
    /\ Cardinality(group) >= 1 /\ Cardinality(group) <= 2
    /\ \A b \in Banks :
         LET after == IF b = boatAt
                      THEN onBank[b] \ group
                      ELSE onBank[b] \cup group
         IN (Missionaries \subseteq after) \/ (Cardinality(after \cap Cannibals) <= Cardinality(after \cap Missionaries))

Move(group) ==
    /\ group \subseteq onBank[boatAt]
    /\ SafeAfterCross(group)
    /\ onBank' = [onBank EXCEPT ![boatAt] = @ \ group, ![NextBank(boatAt)] = @ \cup group]
    /\ boatAt' = NextBank(boatAt)

Next ==
    \E group \in SUBSET People : Move(group)

\* On every bank, missionaries are not outnumbered by cannibals; the boat
\* always carries at least one person and at most two.
Solution ==
    /\ \A b \in Banks :
         (Missionaries \subseteq onBank[b]) \/ (Cardinality(onBank[b] \cap Cannibals) <= Cardinality(onBank[b] \cap Missionaries))
    /\ Cardinality(onBank[NextBank(boatAt)]) >= 1

Spec == Init /\ [][Next]_vars

TypeOKInv == TypeOK
SolutionInv == Solution
====