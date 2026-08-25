---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

(* Type invariant *)
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer \in Offers) \/ (Offer = {})

(* At most one smoker is smoking at any moment *)
AtMostOne ==
    \A i, j \in Ingredients :
        (Smoking[i] /\ Smoking[j]) => i = j

(* Initial state *)
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(* A smoker whose missing ingredient is i starts smoking *)
Start(i) ==
    /\ Offer \in Offers
    /\ Ingredients \ Offer = {i}
    /\ Smoking[i] = FALSE

(* The smoker holding ingredient i stops smoking *)
Stop(i) ==
    /\ Offer = {}
    /\ Smoking[i] = TRUE

(* Next-state relation *)
Next ==
    \/ \E i \in Ingredients :
          /\ Start(i)
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer' = {}
    \/ \E i \in Ingredients :
          /\ Stop(i)
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

vars == <<Smoking, Offer>>

(* Specification with weak fairness on Next *)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

====