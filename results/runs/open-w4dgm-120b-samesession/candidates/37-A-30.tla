---- MODULE CigaretteSmokers ----
EXTENDS Naturals

\* Smokers each hold an infinite supply of one distinct ingredient.  The dealer
\* offers a subset of ingredients missing exactly one, and the smoker who
\* holds that missing ingredient can smoke.  Safety: at most one smoker smokes.
CONSTANTS Ingredients, Offers

Completed == CHOOSE i \in Ingredients : TRUE

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (SUBSET Ingredients) \union {[none]}

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

CanSmoke(i) == i \notin offer

\* A smoker fires only when its own ingredient fills the dealer's missing slot.
StartSmoking(i) ==
  /\ offer # [none]
  /\ CanSmoke(i)
  /\ \A j \in Ingredients : ~smoking[j]
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = [none]

StopSmoking(i) ==
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ \E i \in Ingredients : StartSmoking(i)
  \/ \E i \in Ingredients : StopSmoking(i)

Spec == Init /\ [][Next]_vars
  /\ \A i \in Ingredients : WF_vars(StartSmoking(i)) /\ WF_vars(StopSmoking(i))

AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

TypeOKInv == TypeOK
====