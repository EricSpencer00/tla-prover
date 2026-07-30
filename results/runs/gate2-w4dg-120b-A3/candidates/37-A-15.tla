---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* smoking[i] is the smoking status of the smoker who holds an infinite supply
\* of ingredient i. offer is the dealer's current table offer: a subset of
\* Ingredients missing exactly one ingredient, or empty while someone smokes.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \subseteq Ingredients

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

\* A smoker begins only if the dealer's offer, plus that smoker's own
\* ingredient, yields the full set -- which holds exactly when the offer is
\* missing that very smoker's ingredient.
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
        /\ i \notin offer
        /\ smoking[i] = FALSE
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
        /\ smoking[i] = TRUE
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

\* A weak fairness condition on the next-state relation guarantees the
\* system keeps making progress (smokers keep lighting up and putting out).
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

\* No two smokers are ever lighting up at the same moment.
AtMostOne == \A i \in Ingredients, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

====