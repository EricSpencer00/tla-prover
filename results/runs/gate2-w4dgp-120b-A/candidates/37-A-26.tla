---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Smokers are identified by the single ingredient they have an infinite supply of.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

\* A smoker can smoke when the dealer's offer, plus that smoker's own ingredient,
\* yields a complete set; only one smoker smokes at a time.
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ ~smoking[i]
         /\ \A j \in Ingredients : j = i \/ j \in offer
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ smoking' = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars /\ WF_vars(StopSmoking)

AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====