---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

SmokingSmokers == Cardinality({i \in Ingredients : smoking[i]})

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup { {} }

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E s \in Offers : offer = s

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
        /\ \A j \in Ingredients : ~(j # i /\ j \in offer)
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
        /\ \A j \in Ingredients : smoking[j] => j = i
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E s \in Offers : offer' = s

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
    /\ WF_vars(StopSmoking)

AtMostOne == SmokingSmokers <= 1

====