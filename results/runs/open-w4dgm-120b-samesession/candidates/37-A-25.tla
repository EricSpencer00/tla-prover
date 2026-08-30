---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {"empty"}

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # "empty"
    /\ \E i \in Ingredients :
         /\ \E o \in Offers : o = offer
         /\ i \notin o
         /\ smoking[i] = FALSE
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = "empty"

StopSmoking ==
    /\ offer = "empty"
    /\ \E i \in Ingredients :
         /\ smoking[i] = TRUE
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A a, b \in Ingredients : (smoking[a] /\ smoking[b]) => (a = b)

TypeOKInv == TypeOK

====