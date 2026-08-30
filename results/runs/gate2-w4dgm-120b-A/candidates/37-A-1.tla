---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

AtMostOne == \A i1, i2 \in Ingredients : (smoking[i1] /\ smoking[i2]) => i1 = i2

ValidOffer(o) == o \subseteq Ingredients /\ Cardinality(o) = Cardinality(Ingredients) - 1

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking(i) ==
  /\ offer # {}
  /\ ~smoking[i]
  /\ offer \cup {i} = Ingredients
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking(i) ==
  /\ offer = {}
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_vars

TypeOK == TypeOK
====