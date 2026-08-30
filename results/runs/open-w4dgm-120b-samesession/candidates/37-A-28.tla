---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[i]: the smoker who holds an infinite supply of ingredient i, and whether they are currently smoking.
\* onTable: the dealer's current offer, empty ({} ) when a smoker is smoking.
VARIABLES smoking, onTable

vars == <<smoking, onTable>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ onTable \in (SUBSET Ingredients) \union {"empty"}

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ onTable \in Offers

\* The single smoker whose ingredient completes the full set is the one who may start.
StartSmoking ==
    /\ onTable # "empty"
    /\ \E i \in Ingredients :
         /\ ~smoking[i]
         /\ onTable \union {i} = Ingredients
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ onTable' = "empty"

\* The dealer waits for the current smoker to stop before offering again.
StopSmoking ==
    /\ onTable = "empty"
    /\ onTable' \in Offers
    /\ smoking' = [i \in Ingredients |-> FALSE]

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
    /\ WF_vars(StartSmoking)
    /\ WF_vars(StopSmoking)

\* No two smokers can ever be smoking at the same moment.
AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) <= 1

TypeOKInv == TypeOK

SpecStateBound == Spec /\ TypeOKInv

====