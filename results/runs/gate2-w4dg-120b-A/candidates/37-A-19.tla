---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokerOn, offer

vars == <<smokerOn, offer>>

TypeOK ==
  /\ smokerOn \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {"Empty"})

NoOneSmoking == \A i \in Ingredients : ~smokerOn[i]

Init ==
  /\ \E i \in Ingredients : smokerOn = [j \in Ingredients |-> j = i]
  /\ \E o \in Offers : offer = o
  /\ NoOneSmoking

StartSmoking ==
  /\ offer # "Empty"
  /\ \E i \in Ingredients :
       /\ offer \cup {i} = Ingredients
       /\ smokerOn[i] = FALSE
       /\ smokerOn' = [smokerOn EXCEPT ![i] = TRUE]
  /\ offer' = "Empty"

StopSmoking ==
  /\ offer = "Empty"
  /\ \E i \in Ingredients :
       /\ smokerOn[i] = TRUE
       /\ smokerOn' = [smokerOn EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

AtMostOne ==
  \A i, j \in Ingredients : (smokerOn[i] /\ smokerOn[j]) => i = j

====