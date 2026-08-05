---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup { {} }

AtMostOne == \A a, b \in Ingredients : (smoking[a] /\ smoking[b]) => a = b

Init ==
  /\ smoking = [a \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoke ==
  /\ offer # {}
  /\ \E a \in Ingredients :
       /\ \A b \in Ingredients : b # a => b \in offer
       /\ smoking[a] = FALSE
       /\ smoking' = [smoking EXCEPT ![a] = TRUE]
  /\ offer' = {}

StopSmoke ==
  /\ offer = {}
  /\ \E a \in Ingredients :
       /\ smoking[a] = TRUE
       /\ smoking' = [smoking EXCEPT ![a] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoke \/ StopSmoke

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StopSmoke) /\ WF_vars(StartSmoke)

====