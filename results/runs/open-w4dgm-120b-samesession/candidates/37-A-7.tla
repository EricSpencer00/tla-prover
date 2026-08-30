---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[i] is the smoking flag of the smoker holding ingredient i; an offer
\* is a subset of Ingredients missing exactly one ingredient (empty means a
\* smoker is currently on the pipe).
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ offer \in Offers

\* An offer that, together with the smoker's own ingredient, covers the full set.
SetComplete(i) == offer \cup {i} = Ingredients

StartSmoking(i) ==
  /\ offer # {}
  /\ SetComplete(i)
  /\ \A j \in Ingredients : smoking[j] = FALSE
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking(i) ==
  /\ offer = {}
  /\ smoking[i] = TRUE
  /\ \A j \in Ingredients : smoking' [j] = FALSE
  /\ \E k \in Offers : offer' = k

Next == \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_vars
  /\ \A i \in Ingredients :
       WF_vars(StartSmoking(i)) /\ WF_vars(StopSmoking(i))

AtMostOne ==
  \A i, j \in Ingredients :
    (smoking[i] /\ smoking[j]) => (i = j)

TypeOKInv == TypeOK
====