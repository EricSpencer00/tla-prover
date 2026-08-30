---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

Rep(ing) == "smokingOf" \o ing

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ \A ing \in Ingredients : smoking[Rep(ing)] \in BOOLEAN
  /\ offer \in Offers \cup {{}}

Init ==
  /\ \A ing \in Ingredients : smoking[Rep(ing)] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  \/ \E ing \in Ingredients :
       /\ offer # {}
       /\ offer \cup {ing} = Ingredients
       /\ ~ \E j \in Ingredients : smoking[Rep(j)]
       /\ smoking' = [smoking EXCEPT ![Rep(ing)] = TRUE]
       /\ offer' = {}
  \/ UNCHANGED <<>>

StopSmoking ==
  /\ offer = {}
  /\ \E ing \in Ingredients :
       /\ smoking[Rep(ing)] = TRUE
       /\ smoking' = [smoking EXCEPT ![Rep(ing)] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A i, j \in Ingredients :
    (smoking[Rep(i)] /\ smoking[Rep(j)]) => i = j

Fairness == WF_vars(StopSmoking)
====