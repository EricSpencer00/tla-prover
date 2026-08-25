---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

(* ---------------------------------------------------------------------- *)
(* Type invariant                                                          *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \subseteq Ingredients

(* ---------------------------------------------------------------------- *)
(* Initial state                                                          *)
(* ---------------------------------------------------------------------- *)
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(* ---------------------------------------------------------------------- *)
(* Action: a smoker starts smoking                                         *)
(* ---------------------------------------------------------------------- *)
Start ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ Smoking[i] = FALSE
          /\ Offer = Ingredients \ {i}
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer' = {}

(* ---------------------------------------------------------------------- *)
(* Action: the currently smoking smoker stops and dealer places new offer *)
(* ---------------------------------------------------------------------- *)
Stop ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

(* ---------------------------------------------------------------------- *)
(* Next-state relation                                                     *)
(* ---------------------------------------------------------------------- *)
Next == Start \/ Stop

(* ---------------------------------------------------------------------- *)
(* Specification                                                          *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<Smoking, Offer>> /\ WF_<<Smoking, Offer>>(Next)

(* ---------------------------------------------------------------------- *)
(* Safety invariant: at most one smoker is smoking                         *)
(* ---------------------------------------------------------------------- *)
AtMostOne ==
    /\ Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

====