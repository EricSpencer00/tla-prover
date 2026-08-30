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
    /\ offer \in Offers

Firing ==
    \E i \in Ingredients :
        /\ offer # "empty"
        /\ i \notin offer
        /\ \A j \in Ingredients : smoking[j] = FALSE
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
        /\ offer' = "empty"

Stopping ==
    \E i \in Ingredients :
        /\ offer = "empty"
        /\ smoking[i] = TRUE
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
        /\ \E o \in Offers : offer' = o

Next == Firing \/ Stopping

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A i \in Ingredients : smoking[i] => (\A j \in Ingredients : j # i => ~smoking[j])

====