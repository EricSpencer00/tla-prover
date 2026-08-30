---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

VARIABLES boatBank, onBank

vars == <<boatBank, onBank>>

\* A bank is safe if it holds no missionaries (nothing to endanger) or the
\* number of cannibals does not exceed the number of missionaries there.
BankSafe(b) ==
    \/ Cardinality(onBank[b] \cap Missionaries) = 0
       \/ Cardinality(onBank[b] \cap Cannibals)
            <= Cardinality(onBank[b] \cap Missionaries)

TypeOK ==
    /\ boatBank \in {"east", "west"}
    /\ onBank \in [ {"east", "west"} -> SUBSET People ]

Init ==
    /\ boatBank = "east"
    /\ onBank = [ b \in {"east", "west"} |-> IF b = "east" THEN People ELSE {} ]

\* The boat moves a non-empty group (size 1 or 2) across, and the move is only
\* enabled if both banks stay safe afterwards.
Move(g) ==
    /\ g \subseteq onBank[boatBank]
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ \A b \in {"east", "west"} : BankSafe(b)
    /\ onBank' = [ onBank EXCEPT ![boatBank] = onBank[boatBank] \ g,
                                 ![IF boatBank = "east" THEN "west" ELSE "east"]
                                    = onBank[IF boatBank = "east" THEN "west"
                                                          ELSE "east"] \cup g ]
    /\ boatBank' = IF boatBank = "east" THEN "west" ELSE "east"

Next ==
    \/ \E g \in SUBSET People : Move(g)

Solution == \A b \in {"east", "west"} : BankSafe(b)

Spec == Init /\ [][Next]_vars

====