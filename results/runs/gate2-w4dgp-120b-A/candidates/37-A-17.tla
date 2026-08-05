---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup { {} }

\* At most one smoker is ever smoking at a time.
AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

\* A smoker can only complete the set when the offer, plus its own
\* ingredient, supplies all of the ingredients.
Complete(i) == offer \cup {i} = Ingredients

Init ==
  /\ \E o \in Offers : offer = o
  /\ smoking = [i \in Ingredients |-> FALSE]

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ Complete(i)
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec == Init /\ [][Next]_vars

Fairness == WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

====