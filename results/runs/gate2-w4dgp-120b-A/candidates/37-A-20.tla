---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => (i = j)

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

\* The dealer places a subset of ingredients on the table; exactly one smoker may
\* find that, together with its own infinite supply, forms the full set.
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
        /\ ~smoking[i]
        /\ (offer \cup {i}) = Ingredients
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

====