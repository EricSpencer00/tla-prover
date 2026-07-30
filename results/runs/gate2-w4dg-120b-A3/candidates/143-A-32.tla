---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

None == "none"
AllPeople == Missionaries \cup Cannibals
Banks == {"east", "west"}
MaxBoat == 2
MinBoat == 1

VARIABLES dock, bank, boat

vars == <<dock, bank, boat>>

RECURSIVE Count(_, _)
Count(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Count(f, S \ {x})

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
    /\ dock \in Banks
    /\ bank \in [Banks -> SUBSET AllPeople]
    /\ boat \in 0 .. MaxBoat

Init ==
    /\ dock = "east"
    /\ bank = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]
    /\ boat = 0

Safe ==
    /\ \A b \in Banks :
        \/ Cardinality(bank[b] \cap Missionaries) = 0
        \/ Cardinality(bank[b] \cap Cannibals) <= Cardinality(bank[b] \cap Missionaries)
    /\ boat \in MinBoat .. MaxBoat

Move ==
    /\ boat >= MinBoat
    /\ boat <= MaxBoat
    /\ \E S \in SUBSET bank[dock] :
         /\ Cardinality(S) = boat
         /\ bank' = [bank EXCEPT ![dock] = bank[dock] \ S,
                               ![IF dock = "east" THEN "west" ELSE "east"] = bank[IF dock = "east" THEN "west" ELSE "east"] \cup S]
    /\ dock' = IF dock = "east" THEN "west" ELSE "east"
    /\ boat' = 0

Board ==
    /\ boat = 0
    /\ \E n \in MinBoat .. MaxBoat :
         /\ Cardinality(bank[dock]) >= n
         /\ boat' = n
    /\ UNCHANGED <<dock, bank>>

Next == Move \/ Board

Spec == Init /\ [][Next]_vars

Solution ==
    /\ \A b \in Banks :
         \/ Cardinality(bank[b] \cap Missionaries) = 0
         \/ Cardinality(bank[b] \cap Cannibals) <= Cardinality(bank[b] \cap Missionaries)
    /\ boat \in MinBoat .. MaxBoat
====