---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, Offer

vars == <<smokerStatus, Offer>>

(* Type correctness invariant *)
TypeOK == /\ smokerStatus \in [Ingredients -> BOOLEAN]
          /\ Offer \in Offers \cup { {} }

(* At most one smoker may be smoking at any time *)
AtMostOne == Cardinality({ i \in Ingredients : smokerStatus[i] }) <= 1

(* Initial state: nobody is smoking and the dealer places a valid offer *)
Init == /\ smokerStatus = [i \in Ingredients |-> FALSE]
        /\ Offer \in Offers

(* A smoker starts smoking when the current offer is non‑empty and his
   ingredient completes the set. The offer is cleared. *)
Start == /\ Offer \in Offers
         /\ ~\E i \in Ingredients : smokerStatus[i] = TRUE
         /\ \E i \in Ingredients :
                /\ i \notin Offer
                /\ smokerStatus' = [smokerStatus EXCEPT ![i] = TRUE]
                /\ Offer' = {}

(* The smoking smoker stops, and the dealer places a new offer *)
Stop == /\ Offer = {}
        /\ \E i \in Ingredients :
                /\ smokerStatus[i] = TRUE
                /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
                /\ Offer' \in Offers

Next == Start \/ Stop

(* Specification with weak fairness on Next *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====