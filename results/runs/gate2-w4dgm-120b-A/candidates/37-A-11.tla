---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[i] is the smoking status of the smoker who holds an infinite supply of ingredient i
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

Init ==
    /\ \A i \in Ingredients: smoking[i] = FALSE
    /\ \E o \in Offers: offer = o

NewOffer ==
    \E o \in Offers: offer = o

StartSmoking(i) ==
    /\ offer # {}
    /\ \E j \in Ingredients: j \notin offer /\ j # i
    /\ \A k \in Ingredients: ~smoking[k]
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking(i) ==
    /\ smoking[i] = TRUE
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ NewOffer

Next ==
    \/ \E i \in Ingredients: StartSmoking(i)
    \/ \E i \in Ingredients: StopSmoking(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A i \in Ingredients: WF_vars(StartSmoking(i))
    /\ \A i \in Ingredients: WF_vars(StopSmoking(i))

AtMostOne ==
    \A i, j \in Ingredients: (smoking[i] /\ smoking[j]) => (i = j)

TypeOKInv == TypeOK

====