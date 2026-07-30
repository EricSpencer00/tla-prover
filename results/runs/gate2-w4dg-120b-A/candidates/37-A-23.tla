---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

RECURSIVE SumSmoking(_)
SumSmoking(S) ==
  IF S = {} THEN 0
  ELSE LET i == CHOOSE x \in S : TRUE IN smoking[i] + SumSmoking(S \ {i})

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ (offer \cup {i}) = Ingredients
       /\ ~smoking[i]
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
        /\ WF_vars(Next)

AtMostOne ==
  SumSmoking(Ingredients) <= 1

====