---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* BoatBank: where the boat is docked; PeopleAt: who is on each bank.
VARIABLES BoatBank, PeopleAt

Banks == {"east", "west"}

TypeOK ==
  /\ BoatBank \in Banks
  /\ PeopleAt \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

\* SafeBank: missionaries, if present, are never outnumbered.
\* A bank with no missionaries is safe regardless of cannibals.
\* BoatOnCrossing: the boat's load is always one or two people.
SafeBank(bt) ==
  LET mis == {p \in PeopleAt[bt] : p \in Missionaries}
      cann == {p \in PeopleAt[bt] : p \in Cannibals}
  IN \/ mis = {}
     \/ Cardinality(cann) <= Cardinality(mis)

BoatOnCrossing ==
  LET loaded == {p \in PeopleAt["east"] : p \in Missionaries \cup Cannibals}
  IN Cardinality(loaded) \in {1, 2}

Init ==
  /\ BoatBank = "east"
  /\ PeopleAt = [bt \in Banks |-> IF bt = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* A non-empty, one- or two-person group boards and moves across, but only if the
\* resulting distribution leaves both banks safe.
Move(g) ==
  /\ g # {}
  /\ g \subseteq PeopleAt[BoatBank]
  /\ Cardinality(g) \in {1, 2}
  /\ LET other == IF BoatBank = "east" THEN "west" ELSE "east"
         newEast == IF BoatBank = "east" THEN PeopleAt["east"] \ g ELSE PeopleAt["east"] \cup g
         newWest == IF BoatBank = "west" THEN PeopleAt["west"] \ g ELSE PeopleAt["west"] \cup g
     IN /\ SafeBank(newEast) /\ SafeBank(newWest)
        /\ PeopleAt' = [east |-> newEast, west |-> newWest]
        /\ BoatBank' = other
  /\ UNCHANGED <<Missionaries, Cannibals>>

Next == \E g \in SUBSET (Missionaries \cup Cannibals) : Move(g)

Solution == \A bt \in Banks : SafeBank(bt)

Spec == Init /\ [][Next]_<<BoatBank, PeopleAt>>

====