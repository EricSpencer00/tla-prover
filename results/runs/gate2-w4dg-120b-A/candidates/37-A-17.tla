---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ \A c \in Ingredients : smoking[c] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E c \in Ingredients :
       /\ \A i \in Ingredients : (i \in offer \/ i = c) <=> TRUE
       /\ smoking[c] = FALSE
       /\ smoking' = [smoking EXCEPT ![c] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E c \in Ingredients :
       /\ smoking[c] = TRUE
       /\ smoking' = [smoking EXCEPT ![c] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A c1, c2 \in Ingredients :
    (smoking[c1] /\ smoking[c2]) => (c1 = c2)

====