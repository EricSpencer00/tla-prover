---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

Begun == {i \in Ingredients : smoking[i]}
AtMostOne == Cardinality(Begun) <= 1

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~ smoking[i]
       /\ offer \cup {i} = Ingredients
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

====