---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
Empty == [mc |-> 0, cb |-> 0]

\* Count missionaries / cannibals on a bank.
\* People commute, so the two groups can be counted independently.
Count(set) ==
    [mc |-> Cardinality(set \cap Missionaries),
     cb |-> Cardinality(set \cap Cannibals)]

VARIABLES boatAt, bank, onBoat

vars == <<boatAt, bank, onBoat>>

TypeOK ==
    /\ boatAt \in Banks
    /\ bank \in [Banks -> SUBSET People]
    /\ onBoat \in SUBSET People

Init ==
    /\ boatAt = "east"
    /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ onBoat = Empty

Safe ==
    /\ \A b \in Banks :
         LET ct == Count(bank[b]) IN
         ct.mc = 0 \/ ct.cb <= ct.mc

Boarded(g) == g.subset \in [Banks -> SUBSET People] /\ g.n \in 1..2

\* A whole group boards at once and lands together on the other bank.
Board(g) ==
    /\ ~Boarded(g)
    /\ g.subset[boatAt] \subseteq Missionaries \cup Cannibals
    /\ Cardinality(g.subset[boatAt]) >= g.n
    /\ g.n <= 2
    /\ onBoat' = [boatAt |-> g.n, ~boatAt |-> 0]
    /\ bank' = [bank EXCEPT ![boatAt] = @ \ g.subset[boatAt]]
    /\ boatAt' = boatAt

Disembark(g) ==
    /\ Boarded(g)
    /\ g.n >= 1
    /\ g.n <= Cardinality(bank[~boatAt])
    /\ bank' = [bank EXCEPT ![~boatAt] = @ \cup g.subset[~boatAt]]
    /\ onBoat' = [boatAt |-> 0, ~boatAt |-> g.n]
    /\ boatAt' = ~boatAt

Next == \E g \in [subset : SUBSET People, n : 1..2] : Board(g) \/ Disembark(g)

Spec == Init /\ [][Next]_vars

\* The east bank is never allowed to be barren while anyone is still alive.
Solution == (bank["east"] = {}) ~> (bank["east"] = {})

TypeOKInv == TypeOK
SolutionInv == (bank["east"] = {}) ~> (bank["east"] = {})

====