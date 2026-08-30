---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[i] = TRUE iff the smoker who holds an infinite supply of
\* ingredient i is the one currently smoking. offer is the dealer's
\* currently displayed combination, or empty when a smoker is lighting.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients) \cup {"empty"}

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* The dealer's offer plus exactly one missing ingredient (the smoker's)
\* completes the set, so exactly one smoker can ever be lit.
StartSmoking(i) ==
    /\ offer # "empty"
    /\ ~smoking[i]
    /\ i \notin offer
    /\ (offer \cup {i}) = Ingredients
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = "empty"

StopSmoking(i) ==
    /\ offer = "empty"
    /\ smoking[i]
    /\ \E o \in Offers : offer' = o
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]

Next ==
    \/ \E i \in Ingredients : StartSmoking(i)
    \/ \E i \in Ingredients : StopSmoking(i)

Spec == Init /\ [][Next]_vars
    /\ \A i \in Ingredients : SF_vars(StartSmoking(i)) /\ WF_vars(StopSmoking(i))

AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) <= 1
TypeOKInv == TypeOK
====