---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokers[i] is the smoking flag of the smoker who holds an infinite supply of ingredient i
VARIABLES smokers, offer

vars == <<smokers, offer>>

TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

\* A smoker can smoke only when the dealer's offer, plus that smoker's own ingredient,
\* completes the full set; the offer is then cleared until the smoker stops.
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ ~smokers[i]
         /\ offer \cup {i} = Ingredients
         /\ smokers' = [smokers EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
         /\ smokers[i]
         /\ smokers' = [smokers EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A i, j \in Ingredients : (smokers[i] /\ smokers[j]) => i = j

TypeOKInv == TypeOK

\* Progress: the system never gets stuck with a smoker smoking forever.
SpecFairness == WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

====