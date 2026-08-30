---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* smokers[i] = TRUE iff the smoker holding an infinite supply of ingredient i is smoking
VARIABLES smokers, currentOffer

vars == <<smokers, currentOffer>>

TypeOK ==
  /\ smokers \in [Ingredients -> BOOLEAN]
  /\ currentOffer \in (SUBSET Ingredients) \cup {"empty"}

Init ==
  /\ smokers = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : currentOffer = o

\* An offer is a subset missing exactly one ingredient; the smoker holding that
\* missing ingredient is the only one who can complete the full set and smoke
StartSmoking(i) ==
  /\ currentOffer # "empty"
  /\ i \notin currentOffer
  /\ smokers[i] = FALSE
  /\ \A j \in Ingredients : smokers[j] = FALSE
  /\ smokers' = [smokers EXCEPT ![i] = TRUE]
  /\ currentOffer' = "empty"

StopSmoking(i) ==
  /\ smokers[i] = TRUE
  /\ smokers' = [smokers EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : currentOffer' = o

Next ==
  \/ \E i \in Ingredients : StartSmoking(i)
  \/ \E i \in Ingredients : StopSmoking(i)

Spec == Init /\ [][Next]_vars

AtMostOne ==
  /\ \A i1 \in Ingredients, i2 \in Ingredients :
        (smokers[i1] /\ smokers[i2]) => i1 = i2
  /\ \A i \in Ingredients : smokers[i] => currentOffer = "empty"

Fairness ==
  /\ \A i \in Ingredients : TRUE
  /\ SF_vars(StopSmoking("any"))
====