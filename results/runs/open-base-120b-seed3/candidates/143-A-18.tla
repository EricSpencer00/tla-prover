---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(* Banks *)
CONSTANTS East, West
BankSet == {East, West}

(* ---------------------------------------------------------------------- *)
(* Variables *)
VARIABLES boatPos, people

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

SafeSet(s) ==
  LET m == s \cap Missionaries
      c == s \cap Cannibals
  IN  (m = {}) \/ (Cardinality(c) <= Cardinality(m))

SafeAfter(afterPeople) ==
  \A b \in BankSet : SafeSet(afterPeople[b])

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ boatPos = East
  /\ people = [East |-> Missionaries \cup Cannibals,
               West |-> {}]

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
  \E grp \subseteq people[boatPos] :
    /\ grp # {}
    /\ Cardinality(grp) \in 1..2
    /\ LET other == IF boatPos = East THEN West ELSE East
           afterPeople == [people EXCEPT
                            ![boatPos] = people[boatPos] \ grp,
                            ![other]   = @ \cup grp]
       IN /\ SafeAfter(afterPeople)
          /\ boatPos' = other
          /\ people'   = afterPeople

(* ---------------------------------------------------------------------- *)
(* Type invariant *)

TypeOK ==
  /\ boatPos \in BankSet
  /\ people \in [BankSet -> SUBSET (Missionaries \cup Cannibals)]
  /\ people[East] \cup people[West] = Missionaries \cup Cannibals
  /\ people[East] \cap people[West] = {}

(* ---------------------------------------------------------------------- *)
(* Solution invariant (non‑emptiness of the east bank) *)

Solution == people[East] # {}

====