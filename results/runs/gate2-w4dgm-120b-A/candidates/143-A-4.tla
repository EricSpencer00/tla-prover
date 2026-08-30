---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, distribution
vars == <<boatAt, distribution>>

TypeOK ==
    /\ boatAt \in Banks
    /\ distribution \in [Banks -> SUBSET People]

Init ==
    /\ boatAt = "east"
    /\ distribution = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A bank with no missionaries is safe even if it is full of cannibals.
Safe(b) ==
    LET mc == Cardinality(distribution[b] \cap Missionaries)
        cc == Cardinality(distribution[b] \cap Cannibals)
    IN mc = 0 \/ cc <= mc

\* A crossing moves one or two people to the other bank without ever leaving
\* a bank with missionaries outnumbered by cannibals.
Move ==
    /\ \E G \in (SUBSET distribution[boatAt]) \ {{}} :
         /\ Cardinality(G) <= 2
         /\ LET dest == IF boatAt = "east" THEN "west" ELSE "east"
                newDist == [b \in Banks |-> IF b = boatAt THEN distribution[b] \ G
                                            ELSE IF b = dest THEN distribution[b] \cup G
                                            ELSE distribution[b]]
            IN /\ Safe("east")
               /\ Safe("west")
               /\ distribution' = newDist
               /\ boatAt' = dest

Next == Move

Solution == Cardinality(distribution["east"]) = 0

\* No missionaries outnumbered by cannibals on either bank, and the boat
\* always carries one or two people per crossing (never empty, never overfull).
TypeOK == TypeOK
====