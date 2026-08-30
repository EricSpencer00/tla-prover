---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ sleeping \in BOOLEAN
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ sleeping = \E i \in Ingredients : smoking[i]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ \E j \in Ingredients \ {i} : j \in offer
       /\ \E k \in Ingredients \ {i} : k \in offer
       /\ smoking[i] = FALSE
       /\ \A j \in Ingredients : (j \in offer) => j # i
       /\ \A j \in Ingredients \ {i} : j \in offer
       /\ sleeping' = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ sleeping' = FALSE
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

AtMostOne == \A i, j \in Ingredients : smoking[i] /\ smoking[j] => i = j
====