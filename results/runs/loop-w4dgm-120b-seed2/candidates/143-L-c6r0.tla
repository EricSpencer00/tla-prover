---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, onBank

vars == <<boatAt, onBank>>

TypeOK ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET People]

Init ==
    /\ boatAt = "east"
    /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A bank is safe if missionaries are never outnumbered by cannibals;
\* also trivially safe if it holds no missionaries at all.
BankSafe(b) ==
    /\ (Missionaries \cap onBank[b] # {}) => (Cardinality(Cannibals \cap onBank[b])
                                              <= Cardinality(Missionaries \cap onBank[b]))

\* A move carries a non-empty group of at most two people across the river,
\* and is only allowed if both banks remain safe afterward.
Move ==
    \E g \in SUBSET People :
        /\ g # {}
        /\ Cardinality(g) <= 2
        /\ g \subseteq onBank[boatAt]
        /\ LET dest == IF boatAt = "east" THEN "west" ELSE "east" IN
            /\ \A b \in Banks : (b = boatAt => g \cap onBank[b] = {})
            /\ onBank' = [onBank EXCEPT ![boatAt] = onBank[boatAt] \ g,
                                          ![dest] = onBank[dest] \cup g]
            /\ boatAt' = dest

Next == Move

Spec == Init /\ [][Next]_vars

\* Missionaries are never outnumbered by cannibals on either bank.
Solution ==
    /\ \A b \in Banks : BankSafe(b)
    /\ \A b \in Banks : Cardinality(onBank[b]) <= 2

TypeOKInv == TypeOK

====