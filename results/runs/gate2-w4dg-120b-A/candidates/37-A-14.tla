---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ i \cup offer = Ingredients
       /\ sleeping = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients : smoking[i] = TRUE
  /\ \E o \in Offers :
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
       /\ offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  /\ \A i \in Ingredients : <<i, TRUE>> \notin {<<j, TRUE>> : j \in Ingredients}
====