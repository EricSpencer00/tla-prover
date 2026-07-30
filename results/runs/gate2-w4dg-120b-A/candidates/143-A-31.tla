---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
MaxOnBank == 2

VARIABLES dock, onBank

RECURSIVE OnBankCount(_, _)
OnBankCount(g, s) ==
    IF s = {} THEN 0
    ELSE LET x == CHOOSE y \in s : TRUE
         IN (IF g[x] THEN 1 ELSE 0) + OnBankCount(g, s \ {x})

\* A bank is safe if it contains only cannibals (no missionaries there to be
\* endangered) or cannibals do not outnumber missionaries.
\* The boat must carry exactly one or two people per crossing.
SafeGroup(g) ==
    /\ OnBankCount(g \ Missionaries, Banks) <= OnBankCount(g \ Missionaries, Banks \cup Cannibals)
    /\ (OnBankCount(g \ Missionaries, Banks) = 0 \/ OnBankCount(g \ Missionaries, Banks) >= OnBankCount(g \ Cannibals, Banks))

TypeOK ==
    /\ dock \in Banks
    /\ onBank \in [Banks -> SUBSET People]

Init ==
    /\ dock = "east"
    /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move(s) ==
    /\ s \subseteq onBank[dock]
    /\ Cardinality(s) \in 1..2
    /\ \A i \in Banks : SafeGroup([g \in People |-> g \in (IF i = dock THEN onBank[i] \ s ELSE onBank[i] \cup s)])
    /\ onBank' = [g \in People |-> IF g \in s THEN dock' ELSE onBank[g]]
    /\ dock' = (IF dock = "east" THEN "west" ELSE "east")

Next == \E s \in SUBSET People : Move(s)

Solution ==
    \A i \in Banks : SafeGroup([g \in People |-> g \in onBank[i]])
    /\ \A i \in Banks : Cardinality(onBank[i]) <= MaxOnBank

Spec == Init /\ [][Next]_<<dock, onBank>>

====