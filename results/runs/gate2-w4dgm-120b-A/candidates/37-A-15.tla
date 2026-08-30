---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

SmokingSmokers == Cardinality({i \in Ingredients : smoking[i]})

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \subseteq Ingredients

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ (offer \cup {i}) = Ingredients
         /\ sleeping \in BOOLEAN
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
         /\ smoking[i] = TRUE
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne == SmokingSmokers <= 1

====