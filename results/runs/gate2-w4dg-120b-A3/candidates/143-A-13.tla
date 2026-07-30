---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

Banks == {"east", "west"}

VARIABLES boat, bankOf

vars == <<boat, bankOf>>

Dest(b) == IF b = "east" THEN "west" ELSE "east"

TypeOK ==
  /\ boat \in Banks
  /\ bankOf \in [People -> Banks]

Init ==
  /\ boat = "east"
  /\ bankOf = [p \in People |-> "east"]

MissionariesOn(b) == Cardinality({p \in Missionaries : bankOf[p] = b})
CannibalsOn(b) == Cardinality({p \in Cannibals : bankOf[p] = b})

BankSafe(b) ==
  \/ MissionariesOn(b) = 0
  \/ CannibalsOn(b) <= MissionariesOn(b)

Move(S) ==
  /\ S \subseteq People
  /\ S # {}
  /\ Cardinality(S) <= 2
  /\ \A p \in S : bankOf[p] = boat
  /\ \A p \in S : BankSafe(boat) => (MissionariesOn(boat) - Cardinality(S \cap Missionaries) >= Cardinality(S \cap Cannibals) - Cardinality(S \cap Missionaries))
  /\ bankOf' = [bankOf EXCEPT ![p \in S] = Dest(boat)]
  /\ boat' = Dest(boat)

Next == \E S \in SUBSET People : Move(S)

Spec == Init /\ [][Next]_vars

Solution ==
  /\ BankSafe("east")
  /\ BankSafe("west")
  /\ boat \in Banks
  /\ bankOf \in [People -> Banks]

====