---- MODULE CigaretteSmokers ----
EXTENDS Integers

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
        /\ i \notin offer
        /\ smoking[i] = FALSE
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

====