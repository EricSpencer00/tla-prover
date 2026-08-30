---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

Variables smoking, offer

\* smoking is the per-ingredient boolean flag for the smoker holding that ingredient
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

\* At most one smoker smoking: the set of ingredients currently associated with smoking is empty or a singleton
AtMostOne ==
    Cardinality({i \in Ingredients : smoking[i]}) <= 1

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ ~smoking[i]
         /\ offer \cup {i} = Ingredients
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}
    /\ UNCHANGED << >>

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
         /\ smoking[i]
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_<<smoking, offer>>

Properties == Spec /\ WF_vars(StopSmoking)
====