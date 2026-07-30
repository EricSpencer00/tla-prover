---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

RECURSIVE SmokingCount(_, _)
SmokingCount(S, f) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE e \in S : TRUE IN f[x] + SmokingCount(S \ {x}, f)

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ (i \cup offer) = Ingredients
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StartSmoking)
        /\ WF_vars(StopSmoking)

AtMostOne ==
  /\ SmokingCount(Ingredients, smoking) <= 1
  /\ \A i \in Ingredients : smoking[i] => offer = {}

====