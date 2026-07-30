---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* A smoker smokes when the dealer's offer, plus their own ingredient, yields
\* the complete set of ingredients. The smoker is identified by the ingredient
\* they privately hold in infinite supply.
Smoker(i) == \E c \in Ingredients : c # i /\ c \cup offer = Ingredients

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ Smoker(i)
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StartSmoking)
        /\ WF_vars(StopSmoking)

\* At most one smoker ever smokes at a time.
AtMostOne ==
  \A i, j \in Ingredients :
    /\ (smoking[i] /\ smoking[j]) => i = j

====