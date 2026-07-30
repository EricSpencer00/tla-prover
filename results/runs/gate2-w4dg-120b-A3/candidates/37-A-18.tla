---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ offer \cup {i} = Ingredients
       /\ smoking[i] = FALSE
       /\ sleeping' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ sleeping' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

TypeOK ==
  /\ sleeping \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

AtMostOne ==
  \A i \in Ingredients : \A j \in Ingredients :
    (sleeping[i] /\ sleeping[j]) => i = j

====