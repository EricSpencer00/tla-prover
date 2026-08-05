---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Smokers are not modelled as separate processes: the mapping below gives the
\* smoking status of the smoker that holds each ingredient.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ \A i \in Ingredients : ~smoking[i]
  /\ \E o \in Offers : offer = o

\* Only a smoker whose ingredient completes the full set may start, and the
\* offer is cleared once someone begins.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in (Ingredients \ offer) :
       /\ ~smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* The empty offer signals that a smoker is mid-action, so stopping also
\* re-installs a new offer chosen nondeterministically.
StopSmoking ==
  /\ offer = {}
  /\ \A i \in Ingredients : ~smoking[i]
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A i \in Ingredients, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====