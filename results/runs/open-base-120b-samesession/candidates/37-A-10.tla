---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

Init ==
  /\ Smoking = [i \in Ingredients |-> FALSE]
  /\ Offer \in Offers

StartSmoking ==
  /\ Offer /= {}
  /\ \E i \in Ingredients :
       /\ Offer = Ingredients \ {i}
       /\ Smoking[i] = FALSE
       /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
       /\ Offer' = {}

StopSmoking ==
  /\ Offer = {}
  /\ \E i \in Ingredients :
       /\ Smoking[i] = TRUE
       /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
       /\ Offer' \in Offers

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec ==
  Init /\ [][Next]_<<Smoking, Offer>> /\ WF_vars(Next)

TypeOK ==
  /\ Smoking \in [Ingredients -> BOOLEAN]
  /\ Offer \in Offers \/ Offer = {}

AtMostOne ==
  Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

====