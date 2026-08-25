---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant                                            *)
TypeOK == 
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer = {} \/ Offer \in Offers)

(* ---------------------------------------------------------------------- *)
(* At most one smoker is smoking                                          *)
AtMostOne == 
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

(* ---------------------------------------------------------------------- *)
(* Initial state: no smoker is smoking and the dealer places a valid offer *)
Init == 
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(* ---------------------------------------------------------------------- *)
(* Action: a smoker starts smoking                                         *)
StartSmoking == 
    /\ Offer # {}                                   \* there is an offer on the table
    /\ \E i \in Ingredients :
          /\ Offer = Ingredients \ {i}              \* the offer is missing exactly i
          /\ Smoking[i] = FALSE                     \* i is not already smoking
          /\ \A j \in Ingredients : (j # i => Smoking[j] = FALSE)  \* no other smoker is smoking
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer'   = {}

(* ---------------------------------------------------------------------- *)
(* Action: the smoker stops and the dealer places a new offer              *)
StopSmoking == 
    /\ Offer = {}                                   \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer'   \in Offers

(* ---------------------------------------------------------------------- *)
(* Next-state relation                                                    *)
Next == StartSmoking \/ StopSmoking

(* ---------------------------------------------------------------------- *)
(* Specification with weak fairness                                        *)
vars == <<Smoking, Offer>>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ---------------------------------------------------------------------- *)
(* The identifiers required by the .cfg file                               *)
\* SPECIFICATION formula
Spec

\* INVARIANTS
TypeOK
AtMostOne

=============================================================================