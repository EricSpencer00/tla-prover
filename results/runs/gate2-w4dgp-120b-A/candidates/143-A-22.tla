---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {0, 1}
WestBank == 1
NoneBank == 2
BoatCap == 2

VARIABLES boat, onBank

vars == <<boat, onBank>>

\* People initially all east, and the east bank is modeled as bank 0.
TypeOK ==
    /\ boat \in Banks \cup {NoneBank}
    /\ onBank \in [Banks -> SUBSET People]

Init ==
    /\ boat = 0
    /\ onBank = [b \in Banks |-> IF b = 0 THEN People ELSE {}]

Safe(b) ==
    LET ms == {x \in onBank[b] : x \in Missionaries}
        cs == {x \in onBank[b] : x \in Cannibals}
    IN \/ ms = {}
       \/ Cardinality(cs) <= Cardinality(ms)

Move(S) ==
    /\ S # {}
    /\ Cardinality(S) <= BoatCap
    /\ S \subseteq onBank[boat]
    /\ Cardinality(S) >= 1
    /\ onBank' = [onBank EXCEPT ![boat] = @ \ S, ![1 - boat] = @ \cup S]
    /\ boat' = 1 - boat

Next == \E S \in SUBSET People : Move(S)

\* The river crossing puzzle is solved once the departure bank is empty.
Solution == onBank[0] # {}

Spec == Init /\ [][Next]_vars

====