---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boat, bank

vars == <<boat, bank>>

RECURSIVE SumF(_, _)
SumF(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumF(f, S \ {x})

RECURSIVE Count(_, _)
Count(p, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN (IF p[x] THEN 1 ELSE 0) + Count(p, S \ {x})

MissionaryCount(b) == Count([g \in Missionaries |-> TRUE], bank[b])
CannibalCount(b) == Count([g \in Cannibals |-> TRUE], bank[b])

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
\* This covers the "only cannibals" special case as well.
BankSafe(b) == (MissionaryCount(b) = 0) \/ (MissionaryCount(b) >= CannibalCount(b))

TypeOK ==
    /\ bank \in [Banks -> SUBSET People]
    /\ boat \in Banks
    /\ MissionaryCount("east") + MissionaryCount("west") = Cardinality(Missionaries)
    /\ CannibalCount("east") + CannibalCount("west") = Cardinality(Cannibals)

Init ==
    /\ boat = "east"
    /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move(g1, g2) ==
    LET gset == {g1, g2}
        c == Cardinality(gset)
        origin == boat
        dest == IF boat = "east" THEN "west" ELSE "east"
    IN
    /\ gset \subseteq bank[origin]
    /\ c \in 1..2
    /\ bank' = [bank EXCEPT ![origin] = @ \ gset, ![dest] = @ \cup gset]
    /\ boat' = dest

Next ==
    \/ \E g1 \in People, g2 \in People : Move(g1, g2)

Spec == Init /\ [][Next]_vars

\* Solution is the specific safety outcome the model checker reports: everyone is
\* off the east bank. Once east is empty, further moves just jam the state space.
Solution == Cardinality(bank["east"]) = 0

====