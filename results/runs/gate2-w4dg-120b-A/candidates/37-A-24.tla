---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ sleeping == {i \in Ingredients : sleeping[i]}
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking(i) ==
  /\ offer # {}
  /\ ~smoking[i]
  /\ \E o \in Offers : (offer \cup {i} = o \cup {i}) /\ \A j \in Ingredients : j # i => o # j
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking(i) ==
  /\ offer = {}
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Next)

AtMostOne ==
  (Cardinality({i \in Ingredients : smoking[i]}) <= 1)

====