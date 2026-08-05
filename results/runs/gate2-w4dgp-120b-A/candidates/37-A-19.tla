---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* Each smoker holds an infinite supply of exactly one ingredient; the smoking
\* flag is indexed by that ingredient.
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

AtMostOne == Cardinality({i \in Ingredients : smoking[i]})

Init ==
    /\ \A i \in Ingredients : ~smoking[i]
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
        /\ ~smoking[i]
        /\ {i} \cup offer = Ingredients
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
    /\ WF_vars(StartSmoking)
    /\ WF_vars(StopSmoking)

====