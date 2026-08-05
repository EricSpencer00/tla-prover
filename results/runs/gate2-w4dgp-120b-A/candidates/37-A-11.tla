---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (Offers \cup {{} })

AtMostOne ==
    /\ (\A a \in Ingredients : ~smoking[a])
       \/ (\A a \in Ingredients : smoking[a])

Init ==
    /\ smoking = [a \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # {}
    /\ \E a \in Ingredients :
        /\ ~smoking[a]
        /\ (offer \cup {a}) = Ingredients
        /\ smoking' = [smoking EXCEPT ![a] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E a \in Ingredients :
        /\ smoking[a]
        /\ smoking' = [smoking EXCEPT ![a] = FALSE]
        /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
    /\ WF_vars(StopSmoking)

====