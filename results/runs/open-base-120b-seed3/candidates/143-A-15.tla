---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* Basic assumptions about the constants *)
ASSUME /\ Missionaries # {}
       /\ Cannibals # {}
       /\ Missionaries ∩ Cannibals = {}
       /\ Cardinality(Missionaries) = 3
       /\ Cardinality(Cannibals) = 3

VARIABLES Boat, Bank

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)
People == Missionaries ∪ Cannibals

East == "East"
West == "West"

Opposite(b) == IF b = East THEN West ELSE East

SafeSet(s) ==
  LET m == Missionaries ∩ s
      c == Cannibals ∩ s
  IN (m = {}) \/ (Cardinality(c) <= Cardinality(m))

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
  /\ Boat ∈ {East, West}
  /\ Bank ∈ [ {East, West} -> SUBSET People ]
  /\ Bank[East] ∪ Bank[West] = People
  /\ Bank[East] ∩ Bank[West] = {}

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
  /\ Boat = East
  /\ Bank = [ East |-> People, West |-> {} ]

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)
Next ==
  ∃ grp ∈ SUBSET Bank[Boat] :
    /\ Cardinality(grp) ∈ 1..2
    /\ LET newEast == IF Boat = East THEN Bank[East] \ grp ELSE Bank[East] ∪ grp,
           newWest == IF Boat = West THEN Bank[West] \ grp ELSE Bank[West] ∪ grp
       IN
          /\ SafeSet(newEast)
          /\ SafeSet(newWest)
          /\ Boat' = Opposite(Boat)
          /\ Bank' = [ East |-> newEast, West |-> newWest ]

(* ---------------------------------------------------------------------- *)
(* Solution predicate – the puzzle is solved when the east bank is empty *)
Solution == Bank[East] = {}

====