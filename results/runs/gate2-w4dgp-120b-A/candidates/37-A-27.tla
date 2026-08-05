---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokers[i] is the unique smoker holding an infinite supply of ingredient i; each
\* smoker smokes at most once, so a boolean per ingredient is enough.
VARIABLES smokers, offer

vars == <<smokers, offer>>

TypeOK ==
  /\ smokers \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

AtMostOne == Cardinality({i \in Ingredients : smokers[i]})

Init ==
  /\ smokers = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ smokers' = [i \in Ingredients |-> IF offer = (Offers \ {{i}}) THEN TRUE ELSE smokers[i]]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E o \in Offers : offer' = o
  /\ smokers' = [i \in Ingredients |-> FALSE]

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars /\ WF_vars(StopSmoking) /\ WF_vars(StartSmoking)

====