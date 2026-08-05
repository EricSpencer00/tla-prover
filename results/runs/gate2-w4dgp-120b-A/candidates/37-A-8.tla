---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

SmokerStates == {FALSE, TRUE}
OffersAreValid == Offers \subseteq SUBSET Ingredients /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

TypeOK ==
  /\ smoking \in [Ingredients -> SmokerStates]
  /\ (offer \in Offers \/ offer = {})

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = FALSE
       /\ i \notin offer
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

====