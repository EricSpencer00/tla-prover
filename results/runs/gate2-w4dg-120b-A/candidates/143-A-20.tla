---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
BoatCap == 2

VARIABLES bank, shore, boat
vars == <<bank, shore, boat>>

RECURSIVE Tally(_, _)
Tally(set, f) ==
  IF set = {} THEN 0
  ELSE LET x == CHOOSE y \in set : TRUE IN f[x] + Tally(set \ {x}, f)

TypeOK ==
  /\ bank \in Banks
  /\ shore \in [Banks -> SUBSET People]
  /\ boat \in SUBSET People
  /\ Cardinality(boat) <= BoatCap

Init ==
  /\ bank = "east"
  /\ shore = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ boat = {}

Move ==
  /\ \E g \in SUBSET People :
       /\ g # {}
       /\ g \subseteq shore[bank]
       /\ Cardinality(g) <= BoatCap
       /\ Cardinality(g) >= 1
       /\ boat' = g
       /\ shore' = [shore EXCEPT ![bank] = shore[bank] \ g]
  /\ \E nb \in Banks :
       /\ nb # bank
       /\ bank' = nb
       /\ shore' = [shore EXCEPT ![nb] = shore[nb] \cup boat]
  /\ boat' = {}

BankSafe(b) ==
  LET m == Tally(shore[b], [p \in People |-> IF p \in Missionaries THEN 1 ELSE 0])
      c == Tally(shore[b], [p \in People |-> IF p \in Cannibals THEN 1 ELSE 0])
  IN (m = 0) \/ (c <= m)

Next == Move

Spec == Init /\ [][Next]_vars

Solution ==
  /\ \A b \in Banks : BankSafe(b)
  /\ (boat = {}) => (Cardinality(boat) >= 1 /\ Cardinality(boat) <= BoatCap)
====