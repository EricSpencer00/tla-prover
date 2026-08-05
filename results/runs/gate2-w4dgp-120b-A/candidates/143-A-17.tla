---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, bank

vars == <<boat, bank>>

Banks == {"east", "west"}

\* TypeOK is the complete safety check: missionaires are never outnumbered
\* by cannibals on any bank that still holds a missionary, and the boat's
\* occupants per crossing is bounded to the two people it can carry.
TypeOK ==
    /\ boat \in Banks
    /\ bank \in [Banks -> SUBSET Missionaries \cup Cannibals]
    /\ \A b \in Banks :
        LET people == Cardinality(bank[b] \cap Missionaries)
            ca == Cardinality(bank[b] \cap Cannibals)
        IN (people = 0) \/ (ca <= people)

Init ==
    /\ boat = "east"
    /\ bank = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* The move is the single, reversible crossing of the whole puzzle, so each
\* action is its own inverse (just swap the banks and the boat).
Move ==
    /\ \E g \in 1..2 :
        \E G \in [Banks -> SUBSET Missionaries \cup Cannibals] :
            /\ G[boat] # {}
            /\ Cardinality(G[boat]) = g
            /\ \A b \in Banks : bank[b] = G[b]
            /\ bank' = [b \in Banks |-> IF b = boat THEN G[boat] \ G[b] ELSE G[boat] \cup G[b]]
    /\ boat' = IF boat = "east" THEN "west" ELSE "east"

Next == Move

\* The puzzle is solved once the east bank is empty; a model checker reporting
\* a violation of this (under no deadlock) is exactly what traces a solution.
Solution == (bank["east"] = {}) \/ (Cardinality(Missionaries \cup Cannibals) = 0)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

====