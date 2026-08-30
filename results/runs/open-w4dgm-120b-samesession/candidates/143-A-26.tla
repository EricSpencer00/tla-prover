---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
Docked == {b \in Banks : b}
Everyone == Missionaries \cup Cannibals

VARIABLES dock, people, crossing

vars == <<dock, people, crossing>>

RECURSIVE OnBank(_)
OnBank(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE
                  IN (IF x \in Missionaries THEN 1 ELSE 0) + OnBank(S \ {x})

TypeOK ==
    /\ dock \in Banks
    /\ people \in [Banks -> SUBSET Everyone]
    /\ crossing \subseteq Everyone
    /\ crossing \cap (people["east"] \cup people["west"]) = {}

Init ==
    /\ dock = "east"
    /\ people = [b \in Banks |-> IF b = "east" THEN Everyone ELSE {}]
    /\ crossing = {}

BankIsSafe(b) ==
    /\ ((people[b] \cup crossing) \cap Missionaries = {}) \/ (OnBank(((people[b] \cup crossing) \cap Missionaries) \cup ((people[b] \cup crossing) \cap Cannibals)) >= OnBank((people[b] \cup crossing) \cap Cannibals))

Move ==
    /\ \E g \in SUBSET (people[dock] \cup crossing) :
         /\ crossing = {}
         /\ Cardinality(g) \in {1, 2}
         /\ crossing' = g
         /\ people' = [people EXCEPT ![dock] = people[dock] \ g]
    /\ \E b \in Banks :
         /\ b # dock
         /\ dock' = b
         /\ people' = [people EXCEPT ![b] = people[b] \cup crossing]
         /\ crossing' = {}
    /\ BankIsSafe(dock)
    /\ BankIsSafe("east")
    /\ BankIsSafe("west")

Next == Move

Solution == people["east"] = {}

TypeOKInv == TypeOK
SolutionInv == Solution

Spec == Init /\ [][Next]_vars

====