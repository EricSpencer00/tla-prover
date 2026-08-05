---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* smoking[i] is the smoking flag of the smoker whose infinite supply is ingredient i.
Complete == {i \in Ingredients : TRUE}

TypeOK ==
  /\ sleeping \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

AtMostOne ==
  \A i1 \in Ingredients, i2 \in Ingredients :
     (smoking[i1] /\ smoking[i2]) => i1 = i2

Init ==
  /\ \E o \in Offers : offer = o
  /\ \A i \in Ingredients : smoking[i] = FALSE

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ offer \cup {i} = Complete
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
               /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

====