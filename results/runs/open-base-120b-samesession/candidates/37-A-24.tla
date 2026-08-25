---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT Ingredients, Offers

VARIABLES Smoking, Offer

vars == <<Smoking, Offer>>

(* Type invariant *)
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in SUBSET Ingredients
    /\ (Offer = {} \/ Offer \in Offers)

(* At most one smoker is smoking *)
AtMostOne ==
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

(* Initial state *)
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(* A smoker starts smoking *)
Start(i) ==
    /\ i \in Ingredients
    /\ Offer # {}
    /\ (Ingredients \ Offer) = {i}
    /\ Smoking[i] = FALSE
    /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
    /\ Offer' = {}

(* The smoker stops and dealer offers a new set *)
Stop(i) ==
    /\ i \in Ingredients
    /\ Offer = {}
    /\ Smoking[i] = TRUE
    /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
    /\ Offer' \in Offers

(* Next-state relation *)
Next ==
    \/ \E i \in Ingredients : Start(i)
    \/ \E i \in Ingredients : Stop(i)

(* Specification with weak fairness on Next *)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

====