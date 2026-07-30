---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

RECURSIVE Smokes(_)
Smokes(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN (IF smoking[x] THEN 1 ELSE 0) + Smokes(S \ {x})

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ (offer = {} \/ (offer \in Offers /\ Cardinality(Ingredients) - Cardinality(offer) = 1))

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ offer \cup {i} = Ingredients
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars /\ WF_vars(StopSmoking)

AtMostOne ==
  Smokes(Ingredients) <= 1

====