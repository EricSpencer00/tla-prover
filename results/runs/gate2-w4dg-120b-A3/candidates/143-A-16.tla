---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatBank, shore, trip

vars == <<boatBank, shore, trip>>

\* Safety: when missionaries are present, cannibals must not outnumber them.
BankOK(b) ==
  LET ms == Cardinality({p \in shore[b] : p \in Missionaries})
      cs == Cardinality({p \in shore[b] : p \in Cannibals})
  IN  (ms = 0) \/ (cs <= ms)

TypeOK ==
  /\ boatBank \in Banks
  /\ shore \in [Banks -> SUBSET People]
  /\ trip \in SUBSET People

Init ==
  /\ boatBank = "east"
  /\ shore = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ trip = {}

\* People board the boat on the current bank, then cross to the other bank.
\* The move is only enabled when the resulting distribution is safe on both banks.
Move(S) ==
  /\ S \subseteq shore[boatBank]
  /\ S # {}
  /\ Cardinality(S) <= 2
  /\ \A b \in Banks \ {boatBank} :
        LET newHere == shore[boatBank] \ S
            newThere == shore[b] \cup S
        IN /\ BankOK(newHere)
           /\ BankOK(newThere)
  /\ shore' = [b \in Banks |-> IF b = boatBank THEN shore[b] \ S
                              ELSE IF b = boatBank' THEN shore[b] \cup S
                              ELSE shore[b]]
  /\ boatBank' = "west" + "east" - boatBank
  /\ trip' = S

Next ==
  \/ \E S \in SUBSET People : Move(S)

TypeOK == TypeOK

\* The boat is never empty and never carries more than two people.
TripSizeOK == Cardinality(trip) >= 1 /\ Cardinality(trip) <= 2

Spec == Init /\ [][Next]_vars

\* No missionaries are ever outnumbered on either bank; the trip size is bounded.
Solution == BankOK("east") /\ BankOK("west") /\ TripSizeOK

====