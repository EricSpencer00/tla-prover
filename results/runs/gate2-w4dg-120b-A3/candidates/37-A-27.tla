---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

RECURSIVE SmokingAtMostOnce(_)
SmokingAtMostOnce(S) ==
  LET sum == Cardinality({i \in Ingredients : S[i] = TRUE})
  IN sum <= 1

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers :
       /\ Cardinality(o) = Cardinality(Ingredients) - 1
       /\ offer' = o
  /\ UNCHANGED smoking

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ \A j \in offer : j # i
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers :
       /\ /\ Cardinality(o) = Cardinality(Ingredients) - 1
          /\ offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne == SmokingAtMostOnce(smoking)

====