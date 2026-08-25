---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

(*---------------------------------------------------------------------*)
(* Type invariant                                                      *)
(*---------------------------------------------------------------------*)
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in (Offers \cup { {} })

(*---------------------------------------------------------------------*)
(* Initial state                                                       *)
(*---------------------------------------------------------------------*)
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(*---------------------------------------------------------------------*)
(* Actions                                                             *)
(*---------------------------------------------------------------------*)

StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ Smoking[i] = FALSE
          /\ Offer \cup {i} = Ingredients
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer' = {}

StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

Next == StartSmoking \/ StopSmoking

(*---------------------------------------------------------------------*)
(* Specification                                                       *)
(*---------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_<<Smoking, Offer>> /\ WF_<<Smoking, Offer>>(Next)

(*---------------------------------------------------------------------*)
(* Safety property: at most one smoker is smoking at any time          *)
(*---------------------------------------------------------------------*)
AtMostOne ==
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

====