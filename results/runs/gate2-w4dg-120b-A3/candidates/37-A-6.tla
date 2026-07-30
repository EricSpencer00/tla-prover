---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

None == CHOOSE e \in Ingredients : TRUE

Init ==
  /\ \E o \in Offers : /\ o # {}
                         /\ \A i \in Ingredients : i \notin o => \A j \in Ingredients : j \in o
                         /\ offer' = o
  /\ smoking' = [i \in Ingredients |-> FALSE]

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
  /\ \E o \in Offers :
       /\ o # {}
       /\ \A x \in Ingredients : x \notin o => \A y \in Ingredients : y \in o
       /\ offer' = o

Next == StartSmoking \/ StopSmoking

AtMostOne ==
  \A i, j \in Ingredients :
    /\ smoking[i] => i = j
    /\ smoking[j] => i = j

Spec == Init /\ [][Next]_vars

====