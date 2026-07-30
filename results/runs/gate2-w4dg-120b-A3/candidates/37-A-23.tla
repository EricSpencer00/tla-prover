---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* A smoker holds an infinite supply of exactly one ingredient and is identified
\* by that ingredient, so the smoking status is a function from Ingredients.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

\* Initially no smoker smokes and the dealer's first offer is nondeterministic.
Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

OnlyOneSmokes ==
  /\ (offer # {}) => (\A i \in Ingredients : ~smoking[i])
  /\ (offer = {}) => (\E! i \in Ingredients : smoking[i])

AbleToSmoke(i) == (Ingredients \ {i}) \subseteq offer

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ AbleToSmoke(i)
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

\* Weak fairness on the next-state relation keeps the system cycling.
Spec == Init /\ [][Next]_vars /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

====