---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

\* Each smoker holds an infinite supply of exactly one ingredient.
\* Smoking is a computed property of that smoker, derived from smoking[ing].
Smokers == Ingredients

TypeOK ==
  /\ smoking \in [Smokers -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

\* At most one smoker may be smoking at any moment.
AtMostOne ==
  \A x \in Smokers, y \in Smokers :
     (smoking[x] /\ smoking[y]) => x = y

Init ==
  /\ \A sm \in Smokers : smoking[sm] = FALSE
  /\ \E o \in Offers : offer = o

\* The dealer offers a subset of ingredients, missing exactly one.
StartSmoking(sm) ==
  /\ offer # {}
  /\ offer \cup {sm} = Ingredients
  /\ \A s \in Smokers : smoking' = [smoking EXCEPT ![s] = (s = sm]
  /\ offer' = {}

StopSmoking(sm) ==
  /\ offer = {}
  /\ smoking[sm]
  /\ smoking' = [smoking EXCEPT ![sm] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \E sm \in Smokers : StartSmoking(sm) \/ StopSmoking(sm)

Spec == Init /\ [][Next]_vars
  /\ \A sm \in Smokers : WF_vars(StartSmoking(sm)) /\ WF_vars(StopSmoking(sm))

\* Every smoker has an infinite supply of one distinct ingredient.
\* Every valid offer is missing exactly one ingredient from the full set.
\* The set of offers is a subset of all ingredient subsets.
Assumptions ==
  /\ \A o \in Offers : Cardinality(Ingredients \ o) = 1
  /\ Offers \subseteq SUBSET Ingredients
====