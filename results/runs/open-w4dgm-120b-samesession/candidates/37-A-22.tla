---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {EMPTY})

EmptySet == {}

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

StartSmoking ==
  /\ offer # EMPTY
  /\ \E i \in Ingredients :
       /\ (offer \cup {i}) = Ingredients
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = EMPTY

StopSmoking ==
  /\ offer = EMPTY
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers :
       /\ offer' = o

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec == Init /\ [][Next]_vars

====