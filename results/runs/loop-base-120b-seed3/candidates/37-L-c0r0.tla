---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC, Temporal

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, offer

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ smokerStatus \in [Ingredients -> BOOLEAN]
    /\ (offer \in Offers) \/ (offer = {})

(* ----------------------------------------------------------------------
   At most one smoker is smoking
   ---------------------------------------------------------------------- *)
AtMostOne ==
    Cardinality({ i \in Ingredients : smokerStatus[i] }) <= 1

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ smokerStatus = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* A smoker whose missing ingredient completes the set starts smoking *)
StartSmoking ==
    /\ offer # {}                                 \* an offer is on the table
    /\ \A i \in Ingredients : ~smokerStatus[i]    \* nobody is currently smoking
    /\ \E i \in Ingredients \ offer :
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = TRUE]
          /\ offer' = {}

(* The currently smoking smoker stops and the dealer places a new offer *)
StopSmoking ==
    /\ offer = {}                                 \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ smokerStatus[i]                      \* i is the smoking smoker
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
          /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

vars == << smokerStatus, offer >>

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====