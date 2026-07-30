---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

\* At most one smoker smokes: at most one ingredient maps to true in
\* the smoking record.
AtMostOne ==
  Cardinality({i \in Ingredients : smoking[i]}) <= 1

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* The dealer clears the offer and the smoker begins; exactly one smoker
\* can be selected because adding its own ingredient completes the set.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ \A j \in Ingredients : (j \in offer \/ j = i) => TRUE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}
  /\ UNCHANGED <<>>

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o
  /\ UNCHANGED <<>>

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

====