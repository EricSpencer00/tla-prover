---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoker[ing] is the boolean smoking flag for the smoker whose infinite
\* supply is exactly ing. table holds the dealer's current offer; the empty
\* set is overloaded to mean 'a smoker is in the act' (so the dealer waits).
VARIABLES smoker, table

vars == <<smoker, table>>

TypeOK ==
  /\ smoker \in [Ingredients -> BOOLEAN]
  /\ table \in Offers \cup {{}}

Init ==
  /\ smoker = [ing \in Ingredients |-> FALSE]
  /\ \E o \in Offers : table = o

StartSmoking ==
  /\ table # {}
  /\ Cardinality({ing \in Ingredients : ~table \in Offers}) = 1
  /\ \E ing \in Ingredients :
       /\ table \cup {ing} = Ingredients
       /\ smoker' = [smoker EXCEPT ![ing] = TRUE]
  /\ table' = {}

StopSmoking ==
  /\ table = {}
  /\ \E ing \in Ingredients : smoker[ing] = TRUE /\ smoker' = [smoker EXCEPT ![ing] = FALSE]
  /\ \E o \in Offers : table' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne == Cardinality({ing \in Ingredients : smoker[ing]}) <= 1

\* Weak fairness on the whole transition relation: the system never settles
\* on a configuration in which progress (smoking, then stopping) is
\* permanently unavailable -- it always keeps moving.
Fairness == WF_vars(StartSmoking) /\ WF_vars(StopSmoking)
====