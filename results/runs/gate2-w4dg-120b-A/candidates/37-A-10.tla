---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

RECURSIVE SumFn(_, _)
SumFn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumFn(f, S \ {x})

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in SUBSET Ingredients

\* At most one smoker smoking: exactly one TRUE in the whole smoking map.
AtMostOne ==
  SumFn(smoking, Ingredients) <= 1

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ offer \cup {i} = Ingredients
       /\ ~smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

====