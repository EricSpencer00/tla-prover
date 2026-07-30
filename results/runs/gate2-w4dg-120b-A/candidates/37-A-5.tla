---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in SUBSET Ingredients

AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) =< 1

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

Begin(i) ==
    /\ offer # {}
    /\ i \notin offer
    /\ \A j \in Ingredients : smoking[j] = FALSE
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

Finish(i) ==
    /\ offer = {}
    /\ smoking[i] = TRUE
    /\ \E o \in Offers : offer' = o
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]

Next ==
    \/ \E i \in Ingredients : Begin(i) \/ Finish(i)

Spec ==
    /\ Init /\ [][Next]_vars
    /\ WF_vars(\E i \in Ingredients : Begin(i))
    /\ WF_vars(\E i \in Ingredients : Finish(i))

====