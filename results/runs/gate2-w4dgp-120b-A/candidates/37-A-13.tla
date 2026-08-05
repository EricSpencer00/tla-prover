---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients

VARIABLES smoking, offer

vars == <<smoking, offer>>

Smoking == {i \in Ingredients : smoking[i]}

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

InitOffer == CHOOSE s \in Offers : s \in Offers
NextOffer == CHOOSE s \in Offers : s \in Offers

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer = InitOffer

StartSmoking(i) ==
  /\ offer # {}
  /\ ~\E j \in Ingredients : smoking[j]
  /\ (~\E k \in offer : k = i)
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking(i) ==
  /\ offer = {}
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ offer' = NextOffer

Next ==
  \/ \E i \in Ingredients : StartSmoking(i)
  \/ \E i \in Ingredients : StopSmoking(i)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(StopSmoking("witness"))

AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====