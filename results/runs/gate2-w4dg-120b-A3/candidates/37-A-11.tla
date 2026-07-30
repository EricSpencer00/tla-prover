---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokerState[i] is the smoking flag of the smoker who holds an infinite supply of
\* ingredient i. table is the dealer's current offer (a subset of Ingredients, or
\* empty to mean a smoker is currently smoking).
VARIABLES smokerState, table

vars == <<smokerState, table>>

TypeOK ==
  /\ smokerState \in [Ingredients -> BOOLEAN]
  /\ table \subseteq Ingredients

Init ==
  /\ smokerState = [i \in Ingredients |-> FALSE]
  /\ table \in Offers

\* An offer is always missing exactly one ingredient, so whichever smoker owns that
\* missing one can complete the set and light up.
Eligible(i) == table = Ingredients \ {i}

StartSmoke(i) ==
  /\ table # {}
  /\ Eligible(i)
  /\ smokerState[i] = FALSE
  /\ \A j \in Ingredients : smokerState[j] = FALSE
  /\ smokerState' = [smokerState EXCEPT ![i] = TRUE]
  /\ table' = {}

StopSmoke(i) ==
  /\ table = {}
  /\ smokerState[i] = TRUE
  /\ smokerState' = [smokerState EXCEPT ![i] = FALSE]
  /\ table' \in Offers

Next ==
  \/ \E i \in Ingredients : StartSmoke(i)
  \/ \E i \in Ingredients : StopSmoke(i)

Spec == Init /\ [][Next]_vars
  /\ \A i \in Ingredients : TRUE

AtMostOne ==
  \A i \in Ingredients, j \in Ingredients : (smokerState[i] /\ smokerState[j]) => i = j

====