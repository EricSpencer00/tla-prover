---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES BoatPos, Bank

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)
Banks == {"East", "West"}

Opposite(pos) == IF pos = "East" THEN "West" ELSE "East"

MissionariesOn(b) == { p \in Bank[b] : p \in Missionaries }
CannibalsOn(b)   == { p \in Bank[b] : p \in Cannibals }

Safe(b) ==
  \/ MissionariesOn(b) = {}
  \/ Cardinality(CannibalsOn(b)) <= Cardinality(MissionariesOn(b))

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ BoatPos \in Banks
  /\ Bank \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
  /\ UNION { Bank[b] : b \in Banks } = Missionaries \cup Cannibals
  /\ \A b1, b2 \in Banks : (b1 # b2) => Bank[b1] \cap Bank[b2] = {}

(* ----------------------------------------------------------------------
   Safety invariant (solution condition)
   ---------------------------------------------------------------------- *)
Solution == \A b \in Banks : Safe(b)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ BoatPos = "East"
  /\ Bank = [b \in Banks |-> IF b = "East" THEN Missionaries \cup Cannibals ELSE {}]

(* ----------------------------------------------------------------------
   Move action
   ---------------------------------------------------------------------- *)
Move ==
  /\ \E grp \in SUBSET Bank[BoatPos] :
        /\ Cardinality(grp) \in 1..2
        /\ LET newBank == 
               [b \in Banks |-> 
                 IF b = BoatPos THEN Bank[b] \ grp
                 ELSE IF b = Opposite(BoatPos) THEN Bank[b] \cup grp
                 ELSE Bank[b]]
           IN /\ BoatPos' = Opposite(BoatPos)
              /\ Bank' = newBank
              /\ \A b \in Banks : Safe(b)

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
  \/ Move
  \/ UNCHANGED <<BoatPos, Bank>>

(* ----------------------------------------------------------------------
   Specification (not required by the .cfg but useful)
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<BoatPos, Bank>>

====