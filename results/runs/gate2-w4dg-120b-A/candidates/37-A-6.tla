---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

Complete == UNION Offers

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in SUBSET Ingredients

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E s \in Offers : offer = s

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ i \notin offer
       /\ offer \cup {i} = Complete
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E s \in Offers : offer' = s

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec == Init /\ [][Next]_vars
  /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====