---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

Smokers == Ingredients
Complete == Ingredients

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE e \in S : TRUE
       IN f[x] + SumOf(f, S \ {x})

VARIABLES smoking, offer

TypeOK ==
  /\ smoking \in [Smokers -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ smoking = [s \in Smokers |-> FALSE]
  /\ offer = CHOOSE o \in Offers : TRUE

AtMostOne ==
  SumOf(smoking, Smokers) <= 1

StartSmoking ==
  /\ offer # {}
  /\ \E s \in Smokers :
       /\ offer \cup {s} = Complete
       /\ smoking[s] = FALSE
       /\ smoking' = [smoking EXCEPT ![s] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E s \in Smokers :
       /\ smoking[s] = TRUE
       /\ smoking' = [smoking EXCEPT ![s] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec == Init /\ [][Next]_<<sleeping, offer>>

Fairness ==
  \A a \in {StartSmoking, StopSmoking} : SF_vars(a)
====