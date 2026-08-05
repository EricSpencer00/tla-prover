---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
AllPeople == Missionaries \cup Cannibals

VARIABLES dock, bank

vars == <<dock, bank>>

OnBank(b, G) == {p \in AllPeople : bank[p] = b}
Count(b, G) == Cardinality({p \in G : bank[p] = b})

TypeOK ==
    /\ dock \in Banks
    /\ bank \in [AllPeople -> Banks]

\* Safety: on any bank, if missionaries are present they are not outnumbered
\* by cannibals (the church rule); the extreme case of a cannibal-only bank is
\* safe, since there are no missionaries to endanger.
Safe(b) ==
    (Count(b, Missionaries) = 0) \/ (Count(b, Cannibals) <= Count(b, Missionaries))

Solution == Safe("east") /\ Safe("west")

Init ==
    /\ dock = "east"
    /\ bank = [p \in AllPeople |-> "east"]

\* Passengers board the boat on its current dock and cross; the move is only
\* allowed if both banks remain safe afterwards, and the boat always carries
\* at least one and at most two people (never empty).
Next ==
    \E group \in SUBSET AllPeople :
        /\ group # {}
        /\ Cardinality(group) <= 2
        /\ \A p \in group : bank[p] = dock
        /\ dock' = (IF dock = "east" THEN "west" ELSE "east")
        /\ bank' = [p \in AllPeople |->
                       IF p \in group THEN (IF dock = "east" THEN "west" ELSE "east") ELSE bank[p]]
        /\ Safe(dock) /\ Safe((IF dock = "east" THEN "west" ELSE "east"))

Spec == Init /\ [][Next]_vars

====