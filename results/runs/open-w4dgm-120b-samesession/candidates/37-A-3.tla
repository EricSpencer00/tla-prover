---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

\* At most one smoker smokes at a time: the smoking flags are never true for
\* two different smokers.
AtMostOne ==
    \A i \in Ingredients, j \in Ingredients :
        (i # j) => ~(smoking[i] /\ smoking[j])

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

\* The chosen smoker's ingredient, plus the dealer's offer, fills the set.
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
        /\ offer \cup {i} = Ingredients
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

Spec == Init /\ [][Next]_vars

\* The weak fairness condition applied to every next-state step guarantees
\* progress: the system never gets stuck in a state with no enabled action.
SpecFairness == WF_vars(Next)

====