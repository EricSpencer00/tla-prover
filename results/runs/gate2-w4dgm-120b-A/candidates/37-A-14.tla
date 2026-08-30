---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[i]: the smoker holding an infinite supply of ingredient i is smoking?
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients) \union {"empty"}

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

\* The dealer offers a subset missing exactly one ingredient. A smoker completes it.
StartSmoking(i) ==
    /\ offer # "empty"
    /\ offer \union {i} = Ingredients
    /\ \A j \in Ingredients : smoking[j] = FALSE
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = "empty"

StopSmoking(i) ==
    /\ offer = "empty"
    /\ smoking[i]
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_vars
    /\ \A i \in Ingredients : WF_vars(StartSmoking(i)) /\ WF_vars(StopSmoking(i))

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

TypeOKInv == TypeOK
====