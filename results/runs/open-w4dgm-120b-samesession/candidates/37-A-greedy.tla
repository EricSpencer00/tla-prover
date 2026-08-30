---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[i] is the smoking flag of the smoker who holds an infinite supply of ingredient i.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

\* A smoker may start only when the dealer's offer, combined with its own ingredient,
\* yields the full set of ingredients; the offer is then cleared.
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

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

TypeOKInv == TypeOK

\* Weak fairness on both actions keeps the system from stalling on either side.
SpecFair == Spec /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

====