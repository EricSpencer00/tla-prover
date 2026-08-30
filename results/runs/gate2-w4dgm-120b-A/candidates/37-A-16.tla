---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients) \cup {{}}

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

StartSmoking(i) ==
    /\ offer # {}
    /\ ~smoking[i]
    /\ offer \cup {i} = Ingredients
    /\ \A j \in Ingredients : ~smoking[j]
    /\ sleeping = {}
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking(i) ==
    /\ smoking[i]
    /\ \A j \in Ingredients : smoking[j] = (j = i)
    /\ \E o \in Offers : offer' = o
    /\ sleeping' = [smoking EXCEPT ![i] = FALSE]

Next ==
    \/ \E i \in Ingredients : StartSmoking(i)
    \/ \E i \in Ingredients : StopSmoking(i)

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A a, b \in Ingredients : (smoking[a] /\ smoking[b]) => (a = b)

TypeOKAndAtMostOne == TypeOK /\ AtMostOne

====