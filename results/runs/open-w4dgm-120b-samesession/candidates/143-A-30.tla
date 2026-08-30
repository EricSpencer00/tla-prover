---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
Pop(S) == Cardinality(S)

VARIABLES boatAt, location

vars == <<boatAt, location>>

TypeOK ==
  /\ boatAt \in Banks
  /\ location \in [Banks -> SUBSET People]

Init ==
  /\ boatAt = "east"
  /\ location = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* Safety: missionaries present on a bank are never outnumbered by cannibals;
\* boat capacity is always respected (1 or 2 people, never empty).
SafeOnBank(b) ==
  \/ (location[b] \cap Missionaries) = {}
  \/ Pop(location[b] \cap Cannibals) <= Pop(location[b] \cap Missionaries)

Move ==
  \E S \in SUBSET location[boatAt] :
    /\ S # {}
    /\ Pop(S) <= 2
    /\ \A b \in Banks : b # boatAt =>
         /\ Pop((location[b] \cup S) \cap Cannibals) <= Pop((location[b] \cup S) \cap Missionaries)
         /\ Pop((location[b] \cup S) \cap Missionaries) <= 3
    /\ location' = [location EXCEPT ![boatAt] = location[boatAt] \ S, ![IF boatAt = "east" THEN "west" ELSE "east"] = location[IF boatAt = "east" THEN "west" ELSE "east"] \cup S]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Next == Move

Solution == (\A b \in Banks : SafeOnBank(b)) /\ Pop(location["east"]) = 0

TypeOKInv == TypeOK
SolutionInv == Solution

Spec == Init /\ [][Next]_vars

====