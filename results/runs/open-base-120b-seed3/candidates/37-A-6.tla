---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, Offer

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer = {} ) \/ Offer \in Offers

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(* ----------------------------------------------------------------------
   Action: a smoker starts smoking
   ---------------------------------------------------------------------- *)
StartSmoking ==
    /\ Offer # {}                     \* an offer is present
    /\ \A i \in Ingredients : ~smoking[i]   \* nobody is smoking
    /\ LET i == CHOOSE j \in Ingredients : j \notin Offer IN
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ Offer' = {}

(* ----------------------------------------------------------------------
   Action: the smoking smoker stops and a new offer appears
   ---------------------------------------------------------------------- *)
StopSmoking ==
    /\ Offer = {}                     \* a smoker is currently smoking
    /\ LET i == CHOOSE j \in Ingredients : smoking[j] = TRUE IN
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next == \/ StartSmoking \/ StopSmoking

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<smoking, Offer>> /\ WF_<<smoking, Offer>>(Next)

(* ----------------------------------------------------------------------
   Safety invariant: at most one smoker is smoking
   ---------------------------------------------------------------------- *)
AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => i = j

====