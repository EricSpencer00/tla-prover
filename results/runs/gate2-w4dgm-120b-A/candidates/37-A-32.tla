---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* For each ingredient, which smoker holds an infinite supply of it, and whether
\* that smoker is currently smoking. The current table offer is either a
\* subset of ingredients (missing exactly one) or empty -- empty means a smoker
\* is in the middle of smoking, so no offer is visible.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup { {} }

RECURSIVE Tot(_, _)
Tot(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Tot(f, S \ {x})

Init ==
  /\ \A ing \in Ingredients : smoking[ing] = FALSE
  /\ offer \in Offers

\* A smoker whose own ingredient completes the full set begins smoking; the
\* offer is cleared while that smoker smokes.
StartSmoking ==
  /\ \E ing \in Ingredients :
       /\ ~smoking[ing]
       /\ \E o \in Offers :
            /\ o \cup {ing} = Ingredients
            /\ offer = {}
            /\ offer' = o
       /\ smoking' = [smoking EXCEPT ![ing] = TRUE]
  /\ offer # {}

StopSmoking ==
  /\ \E ing \in Ingredients :
       /\ smoking[ing]
       /\ offer = {}
       /\ smoking' = [smoking EXCEPT ![ing] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(StopSmoking)

AtMostOne == Tot(smoking, Ingredients) <= 1

\* Every smoker eventually gets a turn to smoke.
SmokeProgress == <>(Tot(smoking, Ingredients) = 1)
====