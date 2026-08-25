---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

(* --------------------------------------------------------------------- *)
(*  State variables                                                     *)
(* --------------------------------------------------------------------- *)
VARIABLES boat, loc

(* --------------------------------------------------------------------- *)
(*  Helper definitions                                                  *)
(* --------------------------------------------------------------------- *)
BANK == {"East", "West"}

People == Missionaries \cup Cannibals

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

MissionariesOn(b, L) == { p \in Missionaries : L[p] = b }
CannibalsOn(b, L)   == { p \in Cannibals   : L[p] = b }

SafeBank(b, L) ==
    \/ Cardinality(MissionariesOn(b, L)) = 0
    \/ Cardinality(CannibalsOn(b, L)) <= Cardinality(MissionariesOn(b, L))

Safe(L) == /\ SafeBank("East", L)
          /\ SafeBank("West", L)

(* --------------------------------------------------------------------- *)
(*  Initial state                                                       *)
(* --------------------------------------------------------------------- *)
Init ==
    /\ boat = "East"
    /\ loc = [p \in People |-> "East"]

(* --------------------------------------------------------------------- *)
(*  Type correctness invariant                                           *)
(* --------------------------------------------------------------------- *)
TypeOK ==
    /\ boat \in BANK
    /\ loc \in [People -> BANK]
    /\ Missionaries \cap Cannibals = {}

(* --------------------------------------------------------------------- *)
(*  Solution predicate (goal)                                           *)
(* --------------------------------------------------------------------- *)
Solution ==
    \A p \in People : loc[p] = "West"

(* --------------------------------------------------------------------- *)
(*  Next-state relation                                                  *)
(* --------------------------------------------------------------------- *)
Next ==
    \E move \subseteq People :
        /\ Cardinality(move) \in 1..2
        /\ \A p \in move : loc[p] = boat
        /\ LET newBoat == Opposite(boat) IN
           /\ boat' = newBoat
           /\ loc' = [p \in People |-> IF p \in move THEN newBoat ELSE loc[p]]
           /\ Safe(loc')
        /\ UNCHANGED << >>  \* no other variables

(* --------------------------------------------------------------------- *)
(*  Specification (optional, not required by the cfg)                    *)
(* --------------------------------------------------------------------- *)
(* Spec == Init /\ [][Next]_<<boat, loc>> *)

====