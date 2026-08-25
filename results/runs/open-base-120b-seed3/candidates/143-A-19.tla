---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES Boat, Bank

(*--algorithm--*)
(* No algorithm, only specifications *)

(* Safety predicate for a set of people on a bank *)
Safe(b) ==
  LET m == Cardinality(b \cap Missionaries) IN
  LET c == Cardinality(b \cap Cannibals) IN
    (m = 0) \/ (c <= m)

(* Initial state *)
Init ==
  /\ Boat = "East"
  /\ Bank = [ "East" |-> Missionaries \cup Cannibals,
              "West" |-> {} ]

(* Move action: transport 1 or 2 people across the river *)
Move ==
  LET cur == Boat
      opp == IF cur = "East" THEN "West" ELSE "East"
  IN
    \E passengers \in SUBSET (Bank[cur]) :
      /\ 1 <= Cardinality(passengers) /\ Cardinality(passengers) <= 2
      /\ Boat' = opp
      /\ Bank' = [Bank EXCEPT ![cur] = Bank[cur] \ passengers,
                               ![opp] = Bank[opp] \cup passengers]
      /\ Safe(Bank'["East"])
      /\ Safe(Bank'["West"])

Next == Move

(* Type correctness invariant *)
TypeOK ==
  /\ Boat \in {"East", "West"}
  /\ Bank \in [ {"East", "West"} -> SUBSET (Missionaries \cup Cannibals) ]
  /\ \A b \in {"East", "West"} : Safe(Bank[b])

(* Invariant that is violated when the puzzle is solved *)
Solution == Bank["East"] # {}

====