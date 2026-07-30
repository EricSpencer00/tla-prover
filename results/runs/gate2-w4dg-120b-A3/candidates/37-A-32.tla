---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

\* The dealer's offers are always subsets of Ingredients missing one ingredient.
\* A smoker can smoke when the offer plus its own infinite ingredient covers all of Ingredients.
\* The offer is cleared (empty) whenever someone is smoking, so the table is empty for that duration.
\* At most one smoker is ever smoking.

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \subseteq Ingredients

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

StartSmoking(i) ==
    /\ offer # {}
    /\ \A j \in Ingredients : (j # i) => (j \in offer)
    /\ ~smoking[i]
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}
    /\ UNCHANGED <<>>

StopSmoking(i) ==
    /\ offer = {}
    /\ smoking[i]
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o
    /\ UNCHANGED <<>>

Next ==
    \/ \E i \in Ingredients : StartSmoking(i)
    \/ \E i \in Ingredients : StopSmoking(i)

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

====