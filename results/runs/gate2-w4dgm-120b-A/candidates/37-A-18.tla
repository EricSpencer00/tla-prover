---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ \A j \in Ingredients \ {i} : j \in offer
       /\ \A j \in Ingredients : (j = i) \/ (j \in offer)
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ offer \subseteq Ingredients
  /\ \A i \in Ingredients : smoking[i] \in BOOLEAN

AtMostOne ==
  \A i \in Ingredients : smoking[i] => \A j \in Ingredients \ {i} : ~smoking[j]

====