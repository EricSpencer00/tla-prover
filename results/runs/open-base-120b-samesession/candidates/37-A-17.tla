---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

(*--- Type constraints -----------------------------------*)
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in (Offers \cup { {} })

(*--- Initial state --------------------------------------*)
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(*--- Actions --------------------------------------------*)
StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ Offer = Ingredients \ {i}
          /\ Smoking[i] = FALSE
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer'   = {}

StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer'   \in Offers

Next == StartSmoking \/ StopSmoking

(*--- Specification --------------------------------------*)
Spec == Init /\ [][Next]_<<Smoking,Offer>> /\ WF_<<Smoking,Offer>>(Next)

(*--- Safety invariant -----------------------------------*)
AtMostOne ==
    \A i, j \in Ingredients :
        (Smoking[i] /\ Smoking[j]) => i = j

====