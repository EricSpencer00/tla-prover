---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Ingredients,
  Offers

VARIABLES
  smoking, offer

vars == <<smoking, offer>>

RECURSIVE SumFn(_, _)
SumFn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumFn(f, S \ {x})

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {{} })

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers :
       /\ Cardinality(o) = Cardinality(Ingredients) - 1
       /\ offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ offer \cup {i} = Ingredients
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
       /\ offer' = {}
  /\ UNCHANGED <<>>

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
       /\ \E o \in Offers :
            /\ Cardinality(o) = Cardinality(Ingredients) - 1
            /\ offer' = o
  /\ UNCHANGED <<>>

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
  SumFn(smoking, Ingredients) <= 1

====