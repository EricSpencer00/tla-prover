---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* The dealer's offer is either a non-empty set of ingredients (always
\* missing exactly one) or empty, which is the signal that a smoker is
\* currently smoking.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \subseteq Ingredients

Init ==
    /\ \A ing \in Ingredients : smoking[ing] = FALSE
    /\ \E o \in Offers : offer = o

\* Exactly one smoker may start: the offered set is non-empty and there is
\* exactly one ingredient not already in the offer.
StartSmoking ==
    /\ offer # {}
    /\ \E ing \in Ingredients :
         /\ ing \notin offer
         /\ smoking' = [smoking EXCEPT ![ing] = TRUE]
    /\ offer' = {}

\* The smoker finishes; the dealer puts down a fresh offer.
StopSmoking ==
    /\ offer = {}
    /\ \E o \in Offers : offer' = o
    /\ \E ing \in Ingredients :
         /\ smoking[ing]
         /\ smoking' = [smoking EXCEPT ![ing] = FALSE]

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Next)

AtMostOne ==
    \A p, q \in Ingredients :
        (smoking[p] /\ smoking[q]) => p = q

====