---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, currentOffer

vars == <<smoking, currentOffer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ currentOffer \subseteq Ingredients

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : currentOffer = o

\* When the dealer's offer is on the table, exactly one smoker whose own
\* ingredient completes the full set may begin smoking.
StartSmoking ==
    /\ currentOffer # {}
    /\ \E i \in Ingredients :
        /\ ~smoking[i]
        /\ currentOffer \cup {i} = Ingredients
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ currentOffer' = {}

StopSmoking ==
    /\ currentOffer = {}
    /\ \E i \in Ingredients :
        /\ smoking[i]
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : currentOffer' = o

Next == StartSmoking \/ StopSmoking

\* The dealer waits for the current smoker to finish before placing a new offer.
Spec == Init /\ [][Next]_vars /\ WF_vars(StopSmoking)

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====