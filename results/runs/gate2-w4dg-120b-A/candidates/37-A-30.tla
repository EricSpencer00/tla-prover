---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ sleeping == [x \in Ingredients |-> FALSE]
    /\ sleeping \notin [Ingredients -> BOOLEAN]
    /\ sleeping \in [Ingredients -> BOOLEAN]
    /\ (\A x \in Ingredients : sleeping[x] = FALSE)
    /\ offer \in Offers \cup {{}}

Init ==
    /\ \E o \in Offers : offer = o
    /\ \A x \in Ingredients : smoking[x] = FALSE

StartSmoking ==
    /\ offer # {}
    /\ \E x \in Ingredients :
         /\ (offer \union {x}) = Ingredients
         /\ smoking[x] = FALSE
         /\ smoking' = [smoking EXCEPT ![x] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E x \in Ingredients :
         /\ smoking[x] = TRUE
         /\ smoking' = [smoking EXCEPT ![x] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(StartSmoking)
    /\ WF_vars(StopSmoking)

AtMostOne ==
    \A x \in Ingredients, y \in Ingredients :
        (smoking[x] /\ smoking[y]) => x = y

====