---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

Matches == CHOOSE i \in Ingredients : TRUE

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (Offers \cup {{}})

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

StartSmoking(i) ==
    /\ offer # {}
    /\ \E o \in Offers : offer = o /\ o \cup {i} = Ingredients
    /\ \A j \in Ingredients : smoking' [j] = (j = i)
    /\ offer' = {}

StopSmoking(i) ==
    /\ offer = {}
    /\ smoking[i]
    /\ \A j \in Ingredients : smoking' [j] = FALSE
    /\ \E o \in Offers : offer' = o

Next ==
    \/ \E i \in Ingredients : StartSmoking(i)
    \/ \E i \in Ingredients : StopSmoking(i)

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

====