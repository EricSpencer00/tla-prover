---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Each smoker is identified by the one ingredient they hold an infinite supply of.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {"empty"}

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

\* Exactly one smoker may smoke at a time, and only once the dealer's offer plus
\* that smoker's own ingredient forms a complete set.
StartSmoking ==
    /\ offer # "empty"
    /\ \E i \in Ingredients :
         /\ \A j \in Ingredients : smoking[j] = FALSE
         /\ offer \cup {i} = Ingredients
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
    /\ WF_vars(StartSmoking)
    /\ WF_vars(StopSmoking)

AtMostOne ==
    \A i1, i2 \in Ingredients :
        (smoking[i1] /\ smoking[i2]) => i1 = i2

TypeOKInv == TypeOK
====