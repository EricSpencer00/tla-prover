---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[i]: whether the smoker holding infinite supply of ingredient i is smoking.
\* offer: the current dealer offer (a subset of Ingredients, or empty while someone smokes).
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in SUBSET Ingredients

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

StartSmoking(i) ==
    /\ offer # {}
    /\ ~smoking[i]
    /\ offer \cup {i} = Ingredients
    /\ \A j \in Ingredients : ~smoking[j]
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking(i) ==
    /\ smoking[i]
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next ==
    \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_vars

AtMostOne == \A i \in Ingredients : smoking[i] => (\A j \in Ingredients : ~smoking[j])

\* Weak fairness: every iteration eventually makes progress (a smoker starts/stops).
Fairness == WF_vars(Next)

====