---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS
    Ingredients,
    Offers

\* smoking[e] tracks whether the smoker who holds an infinite supply of
\* ingredient e is currently smoking. The dealer's offer is a subset of
\* Ingredients missing exactly one ingredient (empty only while a smoker
\* is smoking); when it is empty the single smoker who is smoking stops.
VARIABLES smoking, current

vars == <<smoking, current>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ current \subseteq Ingredients

Init ==
    /\ smoking = [e \in Ingredients |-> FALSE]
    /\ current \in Offers

AnyoneSmoking == \E e \in Ingredients : smoking[e]

StartSmoking ==
    /\ current # {}
    /\ \E e \in Ingredients :
         /\ current \cup {e} = Ingredients
         /\ smoking[e] = FALSE
         /\ smoking' = [smoking EXCEPT ![e] = TRUE]
    /\ current' = {}

StopSmoking ==
    /\ current = {}
    /\ AnyoneSmoking
    /\ \E e \in Ingredients :
         /\ smoking[e] = TRUE
         /\ smoking' = [smoking EXCEPT ![e] = FALSE]
    /\ \E o \in Offers : current' = o

Next == StartSmoking \/ StopSmoking

Spec == INIT Init /\ [][Next]_vars
        /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

AtMostOne ==
    \A e1, e2 \in Ingredients : (smoking[e1] /\ smoking[e2]) => e1 = e2

====