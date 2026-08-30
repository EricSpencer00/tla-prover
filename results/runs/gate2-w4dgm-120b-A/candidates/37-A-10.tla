---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

\* smoking[i] is the smoking flag of the smoker who holds an infinite supply
\* of ingredient i. offer is the dealer's current table, either a non-empty
\* subset of Ingredients or the empty marker meaning a smoker is currently
\* on the table.
TypeOK ==
  /\ /\ sleeping \in BOOLEAN
     /\ \A i \in Ingredients : sleeping \in BOOLEAN
  /\ offer \in Offers \cup { {} }

\* At most one smoker smokes: the number of true flags never exceeds one.
AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) <= 1

Init ==
  /\ \E i \in Ingredients : sleeping = [j \in Ingredients |-> j = i]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ \A j \in Ingredients : j # i => (j \in offer)
       /\ sleeping' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients : sleeping[i] = TRUE /\ sleeping' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
Firing == SF_vars(StartSmoking) /\ WF_vars(StopSmoking)
====