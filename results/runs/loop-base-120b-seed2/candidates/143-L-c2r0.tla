---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------------ *)
(* Definitions *)
Person == Missionaries \cup Cannibals
Banks  == {"East", "West"}
BoatPos == Banks

(* ------------------------------------------------------------------------ *)
(* Variables *)
VARIABLES boatPos, bank

(* ------------------------------------------------------------------------ *)
(* Helper predicates *)

Safe(b) ==
  (Missionaries \cap b = {}) \/ 
  (Cardinality(Cannibals \cap b) <= Cardinality(Missionaries \cap b))

TypeOK ==
  /\ boatPos \in BoatPos
  /\ bank \in [Banks -> SUBSET Person]
  /\ Missionaries # {}
  /\ Cannibals # {}
  /\ Missionaries \cap Cannibals = {}
  /\ bank["East"] \cup bank["West"] = Person

Solution ==
  (* The invariant that the east bank is non‑empty.  Its violation means a
     solution (all persons have crossed). *)
  bank["East"] # {}

(* ------------------------------------------------------------------------ *)
(* Initial state *)

Init ==
  /\ boatPos = "East"
  /\ bank["East"] = Person
  /\ bank["West"] = {}

(* ------------------------------------------------------------------------ *)
(* Next-state relation *)

Next ==
  \E grp \in SUBSET bank[boatPos] :
    /\ (Cardinality(grp) = 1) \/ (Cardinality(grp) = 2)
    /\ LET newBank == 
          [b \in Banks |-> 
             IF b = boatPos 
                THEN bank[b] \ grp 
                ELSE bank[b] \cup grp ]
       IN
         /\ boatPos' = IF boatPos = "East" THEN "West" ELSE "East"
         /\ bank'    = newBank
         /\ Safe(newBank["East"])
         /\ Safe(newBank["West"])

(* ------------------------------------------------------------------------ *)
(* Specification (optional, not required by the cfg) *)

Spec == Init /\ [] [][Next]_<<boatPos, bank>>

(* ------------------------------------------------------------------------ *)
(* Invariants to be checked *)

INVARIANT TypeOK
INVARIANT Solution

====