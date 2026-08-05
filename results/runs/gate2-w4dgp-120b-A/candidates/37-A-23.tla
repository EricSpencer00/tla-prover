---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* One smoker holds an infinite supply of each ingredient; smoking[i] is true iff
\* the smoker owning infinite copies of ingredient i is currently smoking.
TypeOK == /\ smoking \in [Ingredients -> BOOLEAN]
          /\ offer \in Offers \cup {{}}

AtMostOne == (\A i \in Ingredients : ~smoking[i]) \/ (Cardinality({i \in Ingredients : smoking[i]}) = 1)

Init == /\ smoking = [i \in Ingredients |-> FALSE]
        /\ \E o \in Offers: offer = o

StartSmoking == /\ offer # {}
                  /\ \A i \in Ingredients : offer \cup {i} = Ingredients
                  /\ \E i \in Ingredients :
                       /\ ~smoking[i]
                       /\ \A j \in Ingredients : ~smoking[j]
                       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
                  /\ offer' = {}

StopSmoking == /\ offer = {}
                  /\ \E i \in Ingredients :
                       /\ smoking[i]
                       /\ sleeping = {i}
                       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
                  /\ \E o \in Offers: offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

\* Progress: smokers keep getting chances to light up and put out.
Fairness == WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

====