---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ smoking = [g \in Ingredients |-> FALSE]
  /\ \E s \in Offers : offer = s

StartSmoking ==
  /\ offer # {}
  /\ \E g \in Ingredients :
       /\ \A k \in Ingredients : k \notin offer => k = g
       /\ ~smoking[g]
       /\ smoking' = [smoking EXCEPT ![g] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E g \in Ingredients :
       /\ smoking[g]
       /\ smoking' = [smoking EXCEPT ![g] = FALSE]
  /\ \E s \in Offers : offer' = s

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

AtMostOne ==
  \A g1, g2 \in Ingredients : (smoking[g1] /\ smoking[g2]) => g1 = g2

====