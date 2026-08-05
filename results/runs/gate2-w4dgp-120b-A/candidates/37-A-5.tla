---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* A smoker owns exactly one ingredient, identified by the ingredient itself.
Ingredient(ing) == CHOOSE sm \in Smokers : sm = ing

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup { {} }

Init ==
  /\ smoking = [ing \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* The dealer offers a subset; the smoker owning the missing ingredient uses
\* its own supply and the table's to smoke, then the offer is cleared.
StartSmoking ==
  /\ offer # {}
  /\ \E ing \in Ingredients :
       /\ Ingredients \ {ing} = offer
       /\ smoking[ing] = FALSE
       /\ smoking' = [smoking EXCEPT ![ing] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E ing \in Ingredients :
       /\ smoking[ing] = TRUE
       /\ smoking' = [smoking EXCEPT ![ing] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
  /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====