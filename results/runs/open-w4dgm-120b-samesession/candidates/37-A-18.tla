---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* Each smoker holds an infinite supply of exactly one ingredient.
\* Smoking is authorised only when the dealer's offer, plus that smoker's
\* own ingredient, completes the set of all ingredients.

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup { {} }

Init ==
  /\ \A ing \in Ingredients : smoking[ing] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking(ing) ==
  /\ offer # {}
  /\ ~\E j \in Ingredients : smoking[j]
  /\ Ingredients = offer \cup {ing}
  /\ smoking' = [smoking EXCEPT ![ing] = TRUE]
  /\ offer' = {}

StopSmoking(ing) ==
  /\ offer = {}
  /\ smoking[ing]
  /\ smoking' = [smoking EXCEPT ![ing] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ \E ing \in Ingredients : StartSmoking(ing)
  \/ \E ing \in Ingredients : StopSmoking(ing)

Spec == Init /\ [][Next]_vars
  /\ \A ing \in Ingredients : WF_vars(StartSmoking(ing)) /\ WF_vars(StopSmoking(ing))

\* Safety: at most one smoker is ever smoking.
AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

TypeOKInv == TypeOK

====