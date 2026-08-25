---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smoker, Offer

(* ----------------------------------------------------------------------
   Type correctness
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ smoker \in [Ingredients -> BOOLEAN]
    /\ Offer   \in (Offers \cup {∅})

(* ----------------------------------------------------------------------
   Safety: at most one smoker may be smoking
   ---------------------------------------------------------------------- *)
AtMostOne ==
    Cardinality({ i \in Ingredients : smoker[i] }) <= 1

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ smoker = [i \in Ingredients |-> FALSE]
    /\ Offer   \in Offers

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* A smoker whose missing ingredient is the one not offered starts smoking *)
StartSmoking ==
    \E i \in Ingredients :
        /\ Offer = Ingredients \ {i}
        /\ smoker[i] = FALSE
        /\ smoker' = [smoker EXCEPT ![i] = TRUE]
        /\ Offer'   = ∅

(* The currently smoking smoker stops and the dealer places a new offer *)
StopSmoking ==
    \E i \in Ingredients :
        /\ Offer = ∅
        /\ smoker[i] = TRUE
        /\ smoker' = [smoker EXCEPT ![i] = FALSE]
        /\ Offer'   \in Offers

Next == StartSmoking \/ StopSmoking

vars == <<smoker, Offer>>

(* ----------------------------------------------------------------------
   Specification with weak fairness on Next
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====