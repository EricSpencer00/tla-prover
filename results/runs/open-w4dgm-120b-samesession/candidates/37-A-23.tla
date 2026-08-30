---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokers[i] is the smoking flag of the smoker whose infinite supply is i
VARIABLES smokers, offer

vars == <<smokers, offer>>

Smoking == {i \in Ingredients : smokers[i]}
TypeOK ==
  /\ smokers \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ smokers = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* Only one smoker can be enabled by an offer missing exactly one ingredient
StartSmoking(i) ==
  /\ offer # {}
  /\ ~smokers[i]
  /\ offer \cup {i} = Ingredients
  /\ smokers' = [smokers EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking(i) ==
  /\ offer = {}
  /\ smokers[i]
  /\ smokers' = [smokers EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(\E i \in Ingredients : StartSmoking(i))
        /\ WF_vars(\E i \in Ingredients : StopSmoking(i))

AtMostOne ==
  /\ \A i \in Ingredients : smokers[i] => \A j \in Ingredients : i = j \/ ~smokers[j]
  /\ (offer # {} => \A i \in Ingredients : ~smokers[i])

====