---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(*  State variables                                                     *)
(* ---------------------------------------------------------------------- *)

VARIABLES BoatPos, Bank

(* ---------------------------------------------------------------------- *)
(*  Derived sets and helper definitions                                 *)
(* ---------------------------------------------------------------------- *)

People == Missionaries \cup Cannibals

Banks == {"East", "West"}

OtherBank(b) == IF b = "East" THEN "West" ELSE "East"

(* Safety condition for a set of people on a bank *)
Safe(s) ==
  LET m == Cardinality(s \cap Missionaries)
      c == Cardinality(s \cap Cannibals)
  IN  (m = 0) \/ (c <= m)

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                       *)
(* ---------------------------------------------------------------------- *)

Init ==
  /\ BoatPos = "East"
  /\ Bank = [b \in Banks |-> IF b = "East" THEN People ELSE {}]

(* ---------------------------------------------------------------------- *)
(*  Next-state relation                                                  *)
(* ---------------------------------------------------------------------- *)

Next ==
  \E grp \subseteq Bank[BoatPos] :
    /\ Cardinality(grp) \in 1..2               \* boat carries 1 or 2 people
    /\ LET newBank == [b \in Banks |
                        IF b = BoatPos THEN Bank[b] \ grp
                        ELSE IF b = OtherBank(BoatPos) THEN Bank[b] \cup grp
                        ELSE Bank[b]]
       IN /\ Safe(newBank["East"])
          /\ Safe(newBank["West"])
    /\ BoatPos' = OtherBank(BoatPos)
    /\ Bank'    = newBank

(* ---------------------------------------------------------------------- *)
(*  Type correctness invariant                                           *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
  /\ BoatPos \in Banks
  /\ Bank \in [Banks -> SUBSET People]
  /\ \A p \in People : (p \in Bank["East"] ) \/ (p \in Bank["West"])
  /\ \A p \in People : ~(p \in Bank["East"] /\ p \in Bank["West"])

(* ---------------------------------------------------------------------- *)
(*  Solution invariant (goal reached)                                   *)
(* ---------------------------------------------------------------------- *)

Solution ==
  Bank["East"] = {}

(* ---------------------------------------------------------------------- *)
(*  Specification                                                       *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<BoatPos, Bank>>

(* ---------------------------------------------------------------------- *)
(*  The invariants that the model checker must check                      *)
(* ---------------------------------------------------------------------- *)

INVARIANT TypeOK
INVARIANT Solution

====