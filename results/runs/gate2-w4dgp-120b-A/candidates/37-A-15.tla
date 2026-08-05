---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {{} : BOOLEAN})

\* The dealer's next offer is chosen nondeterministically, so progress (weak
\* fairness below) is what keeps the system moving rather than a fixed order.
NextOffer == CHOOSE o \in Offers : TRUE

AtMostOne ==
  /\ \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j
  /\ (offer # {} => \A i \in Ingredients : ~smoking[i])

Init ==
  /\ \A i \in Ingredients : ~smoking[i]
  /\ offer = NextOffer

StartSmoking(i) ==
  /\ offer # {}
  /\ ~smoking[i]
  /\ i \cup offer = Ingredients
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking(i) ==
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ offer' = NextOffer

Next ==
  \E i \in Ingredients :
    \/ StartSmoking(i)
    \/ StopSmoking(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in Ingredients : StartSmoking(i))
  /\ WF_vars(\E i \in Ingredients : StopSmoking(i))

====