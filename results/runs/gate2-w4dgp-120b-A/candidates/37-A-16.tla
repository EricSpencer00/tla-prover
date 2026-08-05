---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

Smoking == {i \in Ingredients : smoking[i]}

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ (offer \in Offers) \/ (offer = {})

Init ==
  /\ sleeping = {i \in Ingredients : FALSE}
  /\ \E o \in Offers : offer = o
  /\ smoking = [i \in Ingredients |-> FALSE]

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ {i} = Ingredients \ offer
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

AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

Progress == WF_vars(Next)

====