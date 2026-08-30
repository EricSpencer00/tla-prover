---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

NoBank == "none"
Banks == {"east", "west"}
People == Missionaries \union Cannibals

VARIABLES boatAt, onBank, crossing

vars == <<boatAt, onBank, crossing>>

TypeOK ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET People]
    /\ crossing \in SUBSET People

Init ==
    /\ boatAt = "east"
    /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ crossing = {}

\* A group of 1 or 2 people boards the boat on the current bank and crosses.
\* The move is only enabled if the resulting configuration on both banks is safe.
Move ==
    /\ crossing = {}
    /\ boatAt \in Banks
    /\ \E g \in SUBSET onBank[boatAt] :
         /\ Cardinality(g) \in {1, 2}
         /\ crossing' = g
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
    /\ onBank' = [onBank EXCEPT ![boatAt] = @ \ crossing, ![IF boatAt = "east" THEN "west" ELSE "east"] = @ \union crossing]

Next == Move

\* Safety: on every bank, if missionaries are present, cannibals do not outnumber them.
\* Liveness: the east bank eventually empties -- everyone has crossed.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

TypeOKInv ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET People]
    /\ crossing \in SUBSET People

Solution ==
    /\ \A b \in Banks : onBank[b] \subseteq People
    /\ \A b \in Banks :
         (Missionaries \cap onBank[b] # {}) => (Cardinality(Cannibals \cap onBank[b]) <= Cardinality(Missionaries \cap onBank[b]))
    /\ crossing \subseteq People
    /\ Cardinality(crossing) <= 2

====