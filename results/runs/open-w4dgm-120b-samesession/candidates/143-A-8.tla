---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boatAtEast, bankPeople

vars == <<boatAtEast, bankPeople>>

Banks == {"east", "west"}

TypeOK ==
  /\ boatAtEast \in BOOLEAN
  /\ bankPeople \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

\* The bank-level safety check: a bank is safe if it has no missionaries
\* (nothing to protect) or if cannibals never outnumber missionaries there.
BankIsSafe(b) ==
  \/ (Missionaries \cap bankPeople[b] = {})
  \/ (Cardinality(Cannibals \cap bankPeople[b]) <= Cardinality(Missionaries \cap bankPeople[b]))

Init ==
  /\ boatAtEast = TRUE
  /\ bankPeople = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* A crossing is always a non-empty group of size at most two; the safety
\* condition must hold on both banks after the move.
Move(g) ==
  /\ Cardinality(g) >= 1 /\ Cardinality(g) <= 2
  /\ g \subseteq bankPeople[IF boatAtEast THEN "east" ELSE "west"]
  /\ bankPeople' = [bankPeople EXCEPT ![IF boatAtEast THEN "east" ELSE "west"] = bankPeople[IF boatAtEast THEN "east" ELSE "west"] \ g,
                                    ![IF boatAtEast THEN "west" ELSE "east"] = bankPeople[IF boatAtEast THEN "west" ELSE "east"] \cup g]
  /\ boatAtEast' = ~boatAtEast
  /\ /\ BankIsSafe("east") /\ BankIsSafe("west")

Next == \E g \in SUBSET (Missionaries \cup Cannibals) : Move(g)

Spec == Init /\ [][Next]_vars

Solution == BankIsSafe("east") /\ BankIsSafe("west")

====