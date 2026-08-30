---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
Sides == {"Missionaries", "Cannibals"}
People == Missionaries \cup Cannibals
SideOf(p) == IF p \in Missionaries THEN "Missionaries" ELSE "Cannibals"

VARIABLES boatAt, banks

vars == <<boatAt, banks>>

RECURSIVE Count(_, _)
Count(S, x) ==
  IF S = {} THEN 0
  ELSE LET y == CHOOSE z \in S : TRUE IN (IF SideOf(y) = x THEN 1 ELSE 0) + Count(S \ {y}, x)

TypeOK ==
  /\ boatAt \in Banks
  /\ banks \in [Banks -> SUBSET People]

Init ==
  /\ boatAt = "east"
  /\ banks = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A move carries a nonempty group (one or two) of people from the current bank
\* to the other side, only if the resulting distribution is safe on both banks.
Next =
  \/ \E g \in SUBSET People :
        /\ g # {}
        /\ g \subseteq banks[boatAt]
        /\ Cardinality(g) <= 2
        /\ LET other == CHOOSE b \in Banks : b # boatAt IN
             /\ banks' = [banks EXCEPT ![boatAt] = banks[boatAt] \ g, ![other] = banks[other] \cup g]
             /\ boatAt' = other
           IN
             /\ (banks[boatAt] \ g = {} \/ Count(banks[boatAt] \ g, "Missionaries") >= Count(banks[boatAt] \ g, "Cannibals"))
             /\ Count(banks[other] \cup g, "Missionaries") >= Count(banks[other] \cup g, "Cannibals")

Next ==
  \/ \E g \in SUBSET People :
        /\ g # {}
        /\ g \subseteq banks[boatAt]
        /\ Cardinality(g) <= 2
        /\ LET other == CHOOSE b \in Banks : b # boatAt IN
             /\ banks' = [banks EXCEPT ![boatAt] = banks[boatAt] \ g, ![other] = banks[other] \cup g]
             /\ boatAt' = other
           IN
             /\ (banks[boatAt] \ g = {} \/ Count(banks[boatAt] \ g, "Missionaries") >= Count(banks[boatAt] \ g, "Cannibals"))
             /\ Count(banks[other] \cup g, "Missionaries") >= Count(banks[other] \cup g, "Cannibals")

\* Safety: missionaries are never outnumbered on either bank.
Solution ==
  /\ \A b \in Banks :
        IF \E p \in banks[b] : SideOf(p) = "Missionaries"
        THEN Count(banks[b], "Cannibals") <= Count(banks[b], "Missionaries")
        ELSE TRUE
  /\ \A b \in Banks : Cardinality(banks[b]) <= 6

====