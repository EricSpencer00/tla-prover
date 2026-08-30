---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

ASSUME Ingredients \subseteq Nat
ASSUME Offers \subseteq SUBSET Ingredients

Smokers == Ingredients
Complete == Ingredients

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Smokers -> BOOLEAN]
  /\ offer \in (SUBSET Ingredients) \union {{}}

Init ==
  /\ \A s \in Smokers : smoking[s] = FALSE
  /\ \E o \in Offers :
       /\ Cardinality(o) = Cardinality(Ingredients) - 1
       /\ o \subseteq Ingredients
       /\ offer = o

StartSmoking(s) ==
  /\ offer # {}
  /\ offer \union {s} = Complete
  /\ \A t \in Smokers : ~smoking[t]
  /\ smoking' = [smoking EXCEPT ![s] = TRUE]
  /\ offer' = {}

StopSmoking(s) ==
  /\ smoking[s]
  /\ smoking' = [smoking EXCEPT ![s] = FALSE]
  /\ \E o \in Offers :
       /\ Cardinality(o) = Cardinality(Ingredients) - 1
       /\ o \subseteq Ingredients
       /\ offer' = o

Next ==
  \E s \in Smokers :
    \/ StartSmoking(s) \/ StopSmoking(s)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(StopSmoking(CHOICE Smoker \in Smokers : smoking[Smoker]))

AtMostOne ==
  \A s, t \in Smokers : (smoking[s] /\ smoking[t]) => s = t

====