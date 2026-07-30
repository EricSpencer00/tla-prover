---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

AllIngredients == Ingredients

\* `smoking` is keyed by the ingredient a smoker is infinitely stocked with.
\* `offer` is empty exactly while someone is smoking, forcing the dealer to wait.
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {AllIngredients})

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E S \in Offers : offer' = S
  /\ UNCHANGED smoking

StartSmoking ==
  /\ offer # AllIngredients
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ i \notin offer
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = AllIngredients

StopSmoking ==
  /\ offer = AllIngredients
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E S \in Offers : offer' = S

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A i1, i2 \in Ingredients :
    (smoking[i1] /\ smoking[i2]) => (i1 = i2)

\* The dealer always eventually gets a fresh offer from the next smoker.
SpecFair == Spec /\ WF_vars(StopSmoking)

====