---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* "smoking" maps each ingredient to the smoking status of the smoker who
\* holds an infinite supply of that ingredient.
Complete == {i \in Ingredients : TRUE}

TypeOK ==
  /\ sleeping \in [Ingredients -> BOOLEAN]
  /\ (offer = {} \/ offer \in Offers)

Init ==
  /\ sleeping = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~sleeping[i]
       /\ offer \cup {i} = Complete
       /\ sleeping' = [sleeping EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ sleeping[i]
       /\ sleeping' = [sleeping EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A i, j \in Ingredients :
     /\ sleeping[i]
     /\ sleeping[j]
     => i = j

\* No new actions needed; the weak fairness on the step relation itself is the
\* required liveness assumption.
====