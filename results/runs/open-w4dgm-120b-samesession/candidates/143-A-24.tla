---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
EastSet == Missionaries \cup Cannibals
WestSet == {}

VARIABLES boatAt, onBank

vars == <<boatAt, onBank>>

RECURSIVE CountOf(_, _)
CountOf(S, T) ==
    IF T = {} THEN 0
    ELSE LET x == CHOOSE y \in T : TRUE IN
         (IF x \in S THEN 1 ELSE 0) + CountOf(S, T \ {x})

TypeOK ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET People]

Init ==
    /\ boatAt = "east"
    /\ onBank = [b \in Banks |-> IF b = "east" THEN EastSet ELSE WestSet]

\* A bank is safe if it holds no missionaries, or cannibals do not outnumber
\* missionaries there. The move must also respect the boat's capacity.
Safe(bank) ==
    \/ (CountOf(Missionaries, onBank[bank]) = 0)
       \/ (CountOf(Cannibals, onBank[bank]) <= CountOf(Missionaries, onBank[bank]))

\* Move a non-empty group of at most two people across; it is the only action.
Move ==
    /\ \E group \in SUBSET People :
         /\ group # {}
         /\ Cardinality(group) <= 2
         /\ group \subseteq onBank[boatAt]
         /\ LET dest == (IF boatAt = "east" THEN "west" ELSE "east")
                newOnBank == [onBank EXCEPT ![boatAt] = onBank[boatAt] \ group,
                                          ![dest] = onBank[dest] \cup group]
            IN /\ newOnBank["east"] \cap newOnBank["west"] = {}
               /\ Safe("east") /\ Safe("west")
         /\ onBank' = newOnBank
    /\ boatAt' = (IF boatAt = "east" THEN "west" ELSE "east")

Next == Move

\* Progress is safe and respects the boat's capacity.
Solution == TypeOK /\ \A bank \in Banks : Safe(bank)
====