---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {"empty"}

Init ==
  /\ \A g \in Ingredients : smoking[g] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # "empty"
  /\ \E g \in Ingredients :
       /\ \A h \in Ingredients : (h \in offer \cup {g}) = TRUE
       /\ smoking[g] = FALSE
       /\ smoking' = [smoking EXCEPT ![g] = TRUE]
  /\ offer' = "empty"

StopSmoking ==
  /\ offer = "empty"
  /\ \E g \in Ingredients :
       /\ smoking[g] = TRUE
       /\ smoking' = [smoking EXCEPT ![g] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A g1, g2 \in Ingredients :
    (smoking[g1] /\ smoking[g2]) => g1 = g2

====