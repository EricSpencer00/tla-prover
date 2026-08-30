---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokers[i]: true iff the smoker who holds infinite supply of ingredient i
\* is currently smoking. offer: the subset of ingredients (missing exactly
\* one) the dealer currently has on the table; {} means someone is smoking.
VARIABLES smokers, offer

vars == <<smokers, offer>>

TypeOK ==
  /\ smokers \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

AtMostOne ==
  \A i, j \in Ingredients : (smokers[i] /\ smokers[j]) => i = j

Init ==
  /\ smokers = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ smokers' = [i \in Ingredients |-> IF i = THE (Ingredients \ offer) THEN TRUE ELSE FALSE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients : smokers[i] = TRUE /\ smokers' = [smokers EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

Fairness == WF_vars(StopSmoking)

====