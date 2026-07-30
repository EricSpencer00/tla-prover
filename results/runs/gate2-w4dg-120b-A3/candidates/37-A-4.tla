---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[i] is the smoking flag of the smoker who holds an infinite supply of
\* ingredient i; exactly one smoker is ever smoking at a time.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

AllFalse == \A i \in Ingredients : ~smoking[i]

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ offer \in Offers

\* A smoker starts only when its own ingredient completes the full set.
StartSmoke(i) ==
  /\ offer # {}
  /\ \A k \in Ingredients \ {i} : k \in offer
  /\ smoking[i] = FALSE
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoke(i) ==
  /\ offer = {}
  /\ smoking[i] = TRUE
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ \E i \in Ingredients : StartSmoke(i)
  \/ \E i \in Ingredients : StopSmoke(i)

Spec == Init /\ [][Next]_vars

\* At most one smoker is ever smoking at the same time.
AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====