---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* `smoking` maps each ingredient to the smoking status of the smoker who
\* holds an infinite supply of that ingredient. `offer` is the dealer's
\* current offer, or empty (meaning a smoker is currently smoking).
TypeOK ==
  /\ sleeping \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ sleeping = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ \A j \in (Ingredients \ {i}) : j \in offer
       /\ sleeping[i] = FALSE
       /\ sleeping' = [sleeping EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ sleeping' \in [Ingredients -> BOOLEAN]
  /\ \E o \in Offers :
       /\ offer' = o
       /\ \A i \in Ingredients : ~(sleeping[i] = TRUE /\ (sleeping' = [sleeping EXCEPT ![i] = FALSE]))

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
          /\ WF_vars(StopSmoking)

AtMostOne ==
  \A i, j \in Ingredients :
    (sleeping[i] /\ sleeping[j]) => i = j

====