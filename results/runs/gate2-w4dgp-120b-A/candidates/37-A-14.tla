---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokingOf, offer
vars == <<smokingOf, offer>>

TypeOK ==
  /\ sleepingOf \in [Ingredients -> BOOLEAN]
  /\ offer \in { {}, NULL } \cup Offers

AtMostOne ==
  Cardinality({ i \in Ingredients : sleepingOf[i] }) <= 1

Init ==
  /\ \A i \in Ingredients : sleepingOf[i] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ offer \cup {i} = Ingredients
       /\ sleepingOf[i] = FALSE
       /\ sleepingOf' = [sleepingOf EXCEPT ![i] = TRUE]
  /\ offer' = {}
  
StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ sleepingOf[i] = TRUE
       /\ sleepingOf' = [sleepingOf EXCEPT ![i] = FALSE]
       /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
====