---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* A smoker is identified by the single ingredient it has in infinite supply.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* Starting a smoke clears the offer; the single smoker is the one whose own
\* ingredient completes the set.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ offer \cup {i} = Ingredients
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
        /\ WF_vars(Next)

AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

====