---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
\* The two banks of the river; Missionaries and Cannibals are the two sides
\* of the classic puzzle's people set.

VARIABLES boatBank, bankPop

vars == <<boatBank, bankPop>>

TypeOK ==
    /\ boatBank \in Banks
    /\ bankPop \in [Banks -> SUBSET People]

Init ==
    /\ boatBank = "east"
    /\ bankPop = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A crossing moves a non-empty group of size at most two across and leaves both
\* banks safe, i.e. missionaries are never outnumbered on either side.
Move ==
    /\ \E g \in SUBSET People :
         /\ g # {}
         /\ Cardinality(g) <= 2
         /\ g \subseteq bankPop[boatBank]
         /\ LET other == IF boatBank = "east" THEN "west" ELSE "east" IN
              /\ bankPop' = [bankPop EXCEPT ![boatBank] = @ \ g, ![other] = @ \cup g]
              /\ boatBank' = other
         /\ (\A b \in Banks :
               (bankPop[b] \cap Missionaries = {}) \/ (Cardinality(bankPop[b] \cap Cannibals) <= Cardinality(bankPop[b] \cap Missionaries)))
    /\ UNCHANGED <<>>

Next == Move

Solution == bankPop["east"] # {}

====