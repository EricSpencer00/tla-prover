---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ sleeping == {i \in Ingredients : smoking[i]}
  /\ offer \in Offers \cup {{}}

Init ==
  /\ sleeping == {}
  /\ \E o \in Offers : offer = o

OfferAny ==
  {o \in Offers : Cardinality(Ingredients \ o) = 1}

StartSmoking ==
  \E i \in Ingredients :
    /\ offer # {}
    /\ Ingredients \ offer = {i}
    /\ sleeping = {}
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
  /\ sleeping # {}
  /\ \E o \in OfferAny : offer' = o
  /\ smoking' = [i \in Ingredients |-> FALSE]

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====