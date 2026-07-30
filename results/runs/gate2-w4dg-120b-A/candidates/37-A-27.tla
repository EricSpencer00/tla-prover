---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {0})

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

Begin ==
  /\ offer # 0
  /\ \E i \in Ingredients :
       /\ offer \cup {i} = Ingredients
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = 0

Finish ==
  /\ offer = 0
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ Begin
  \/ Finish

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Finish)

AtMostOne ==
  \A i, j \in Ingredients :
    (smoking[i] /\ smoking[j]) => i = j

====