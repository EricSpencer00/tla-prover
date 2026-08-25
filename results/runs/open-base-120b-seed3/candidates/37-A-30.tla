---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, Temporal

CONSTANTS Ingredients, Offers

VARIABLES smokerState, Offer

(*-------------------------------------------------------------------*)
(* Type correctness                                                    *)
(*-------------------------------------------------------------------*)
TypeOK ==
    /\ smokerState \in [Ingredients -> BOOLEAN]
    /\ Offer \in Offers \/ { {} }

(*-------------------------------------------------------------------*)
(* Initial state                                                       *)
(*-------------------------------------------------------------------*)
Init ==
    /\ smokerState = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(*-------------------------------------------------------------------*)
(* Helper: ingredient missing from the current offer                    *)
(*-------------------------------------------------------------------*)
MissingIngredient(offer) == Ingredients \ offer

(*-------------------------------------------------------------------*)
(* Action: a smoker starts smoking                                      *)
(*-------------------------------------------------------------------*)
StartSmoking ==
    /\ Offer # {}
    /\ LET miss == MissingIngredient(Offer) IN
          /\ Cardinality(miss) = 1
          /\ \E i \in miss :
                /\ smokerState[i] = FALSE
                /\ smokerState' = [smokerState EXCEPT ![i] = TRUE]
    /\ Offer' = {}

(*-------------------------------------------------------------------*)
(* Action: the smoking smoker stops and dealer places a new offer      *)
(*-------------------------------------------------------------------*)
StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ smokerState[i] = TRUE
          /\ smokerState' = [smokerState EXCEPT ![i] = FALSE]
    /\ Offer' \in Offers

(*-------------------------------------------------------------------*)
(* Next-state relation                                                  *)
(*-------------------------------------------------------------------*)
Next ==
    \/ StartSmoking
    \/ StopSmoking

vars == <<smokerState, Offer>>

(*-------------------------------------------------------------------*)
(* Specification                                                       *)
(*-------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

(*-------------------------------------------------------------------*)
(* Safety invariant: at most one smoker is smoking at any time        *)
(*-------------------------------------------------------------------*)
AtMostOne ==
    \A i, j \in Ingredients :
        (smokerState[i] /\ smokerState[j]) => i = j

====