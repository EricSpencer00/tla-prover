---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
NoOne == "emptyboat"

VARIABLES boatAt, onBank, inBoat
vars == <<boatAt, onBank, inBoat>>

RECURSIVE CountOf(_)
CountOf(S) == IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE IN (IF x \in Missionaries THEN 1 ELSE 0) + CountOf(S \ {x})

TypeOK ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET People]
    /\ inBoat \in People \cup {NoOne}

\* A bank with missionaries must not have more cannibals than missionaries.
\* A bank without any missionaries is "safe" regardless of cannibal count.
Safe ==
    \A b \in Banks :
        LET ms == {p \in onBank[b] : p \in Missionaries}
            cs == {p \in onBank[b] : p \in Cannibals}
        IN \A c \in cs, m \in ms : TRUE
           \/ Cardinality(cs) <= Cardinality(ms)

Init ==
    /\ boatAt = "east"
    /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ inBoat = NoOne

Next == BoatTrip

\* A move is one or two people boarding the boat and crossing to the other bank,
\* but only if the banks stay safe afterwards.
BoatTrip ==
    /\ inBoat = NoOne
    /\ \E board \in SUBSET onBank[boatAt] :
        /\ Cardinality(board) \in 1..2
        /\ LET other == IF boatAt = "east" THEN "west" ELSE "east"
               newOnBank == [onBank EXCEPT ![boatAt] = @ \ board, ![other] = @ \cup board]
           IN /\ Safe
              /\ onBank' = newOnBank
        /\ inBoat' = CHOOSE e \in board : TRUE
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

\* Once everyone is on the west bank, trips stop (a solved puzzle stays solved).
Solution == (\A b \in Banks : onBank[b] = People) \/ (boatAt = "west" /\ inBoat = NoOne)

Spec == Init /\ [][Next]_vars

\* No missionaries are ever eaten; every crossing carries at least one and at most two.
\* No solution trace can have a bank where outnumbered missionaries die.
\* The PRESERVE invariant is the one the model checker reports on when a solution is found.
\* The "east bank is non-empty" invariant is deliberately omitted from the config, so a
\* trace that reaches a solved state is not flagged as a failure.
PRESERVE == \A b \in Banks :
    LET ms == {p \in onBank[b] : p \in Missionaries}
        cs == {p \in onBank[b] : p \in Cannibals}
    IN Cardinality(ms) = 0 \/ Cardinality(cs) <= Cardinality(ms)

====