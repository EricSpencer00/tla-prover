---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>
Full == Ingredients

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \subseteq Ingredients

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ i \notin offer
         /\ ~smoking[i]
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
         /\ smoking[i]
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Next)

AtMostOne ==
    \A i \in Ingredients : \A j \in Ingredients :
        (smoking[i] /\ smoking[j]) => (i = j)

====