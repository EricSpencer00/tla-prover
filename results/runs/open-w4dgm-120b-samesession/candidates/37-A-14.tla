---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

AtMostOne ==
    Cardinality({p \in Ingredients : smoking[p]}) <= 1

Init ==
    /\ \A p \in Ingredients : smoking[p] = FALSE
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # {}
    /\ \E p \in Ingredients :
         /\ offer \cup {p} = Ingredients
         /\ smoking[p] = FALSE
         /\ smoking' = [smoking EXCEPT ![p] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E p \in Ingredients :
         /\ smoking[p] = TRUE
         /\ smoking' = [smoking EXCEPT ![p] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

====