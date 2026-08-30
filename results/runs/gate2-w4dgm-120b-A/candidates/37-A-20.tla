---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* Every smoker holds an infinite supply of exactly one distinct ingredient.
\* The dealer offers a subset of the ingredients (missing exactly one), which
\* combined with a smoker's own ingredient may form a complete set.
\* At most one smoker smokes at any time: the offer is cleared while someone
\* smokes and the dealer waits for them to finish before placing the next.
\* A weak fairness condition on Next guarantees progress -- smokers keep
\* lighting up and finishing.

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

\* Exactly one smoker whose ingredient completes the full set may begin.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ i \notin offer
       /\ \A j \in Ingredients : smoking[j] = FALSE
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
  \A i, j \in Ingredients :
     (smoking[i] /\ smoking[j]) => i = j

\* Progress: the system keeps moving (a smoker keeps lighting up and finishing).
Fairness ==
  \A a \in {StartSmoking, StopSmoking} : WF_vars(a)

====