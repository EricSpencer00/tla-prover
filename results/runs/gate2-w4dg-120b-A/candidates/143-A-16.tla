---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
LoadOpts == {{p} : p \in People} \cup {{p, q} : p, q \in People}

VARIABLES boatBank, bankOf

vars == <<boatBank, bankOf>>

RECURSIVE CountIn(_, _)
CountIn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + CountIn(f, S \ {x})

LoadAt(b) == {p \in People : bankOf[p] = b}

MissionaryCount(b) == CountIn([p \in People |-> IF p \in Missionaries THEN 1 ELSE 0], {p \in People : bankOf[p] = b})
CannibalCount(b) == CountIn([p \in People |-> IF p \in Cannibals THEN 1 ELSE 0], {p \in People : bankOf[p] = b})

TypeOK ==
  /\ boatBank \in Banks
  /\ bankOf \in [People -> Banks]

Init ==
  /\ boatBank = "east"
  /\ bankOf = [p \in People |-> "east"]

\* A bank is safe if it has no missionaries, or cannibals are not outnumbering them.
BankSafe(b) == (MissionaryCount(b) = 0) \/ (CannibalCount(b) <= MissionaryCount(b))

\* Boat always carries one or two people, never zero (when it moves).
Move ==
  /\ \E group \in LoadOpts :
       /\ group \subseteq LoadAt(boatBank)
       /\ Cardinality(group) \in {1, 2}
       /\ LET other == IF boatBank = "east" THEN "west" ELSE "east" IN
            /\ bankOf' = [bankOf EXCEPT ![p] = other : p \in group]
            /\ boatBank' = other
  /\ /\ BankSafe("east")
     /\ BankSafe("west")

Next ==
  \/ Move

Spec ==
  /\ Init
  /\ [][Next]_vars

\* The puzzle is solved when no one is left on the east bank.
Solution ==
  /\ BoatBank = "west"
  /\ \A p \in People : bankOf[p] = "west"

====