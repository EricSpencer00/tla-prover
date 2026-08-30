---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

Smokers == Ingredients
AllHere == Ingredients

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Smokers -> BOOLEAN]
  /\ offer \in (SUBSET Ingredients) \cup {AllHere}

Init ==
  /\ \A s \in Smokers : smoking[s] = FALSE
  /\ \E a \in Offers : offer = a

StartSmoking(s) ==
  /\ offer # AllHere
  /\ offer # {}
  /\ (offer \cup {s}) = AllHere
  /\ \A q \in Smokers : smoking[q] = FALSE
  /\ smoking' = [smoking EXCEPT ![s] = TRUE]
  /\ offer' = AllHere

StopSmoking(s) ==
  /\ offer = AllHere
  /\ smoking[s] = TRUE
  /\ \A q \in Smokers : smoking' = [smoking EXCEPT ![s] = FALSE]
  /\ \E a \in Offers : offer' = a

Next ==
  \/ \E s \in Smokers : StartSmoking(s)
  \/ \E s \in Smokers : StopSmoking(s)

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A p, q \in Smokers : (smoking[p] /\ smoking[q]) => p = q

\* Weak fairness on every transition keeps the action set live, so the system
\* does not get stuck once every smoker has had a turn.
Fairness == WF_vars(Next)
====