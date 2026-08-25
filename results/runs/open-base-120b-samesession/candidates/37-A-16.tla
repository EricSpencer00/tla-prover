---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

(* -------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
    Smoking \in [Ingredients -> BOOLEAN] /\
    (Offer = {} \/ Offer \in Offers)

(* -------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(* -------------------------------------------------------------------- *)
(* A smoker starts smoking *)
Start ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          (i \notin Offer) /\ (Offer \cup {i}) = Ingredients
          /\ Smoking[i] = FALSE
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer' = {}

(* -------------------------------------------------------------------- *)
(* The smoker stops smoking *)
Stop ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

(* -------------------------------------------------------------------- *)
Next == Start \/ Stop

(* -------------------------------------------------------------------- *)
(* Specification with weak fairness on Next *)
Spec == Init /\ [][Next]_<<Smoking, Offer>> /\ WF_<<Smoking, Offer>>(Next)

(* -------------------------------------------------------------------- *)
(* Safety: at most one smoker is smoking *)
AtMostOne == Cardinality({i \in Ingredients : Smoking[i]}) <= 1

====