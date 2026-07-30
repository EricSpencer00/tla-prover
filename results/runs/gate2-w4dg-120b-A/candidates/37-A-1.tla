---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in SUBSET Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ i \notin offer
       /\ smoking[i] = FALSE
       /\ \A j \in Ingredients : ~(j \in offer \/ j = i) => FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
       /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  /\ \A i \in Ingredients, j \in Ingredients :
       (smoking[i] /\ smoking[j]) => i = j

====