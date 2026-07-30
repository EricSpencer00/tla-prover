---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* A smoker owns one ingredient and is identified by it; the boolean flags
\* record whether that smoker is currently smoking.
TypeOK ==
  /\ sleeping \in BOOLEAN
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {{} \cup Ingredients})

AtMostOne ==
  Cardinality({i \in Ingredients : smoking[i]}) <= 1

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ offer \in Offers

\* The smoker who holds the missing ingredient completes the full set.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ \A j \in Ingredients : j \in offer \/ j = i
       /\ smoking[i] = FALSE
       /\ sleeping = FALSE
       /\ sleeping' = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
       /\ offer' = {}

\* The single smoker on the table finishes; the dealer offers again.
StopSmoking ==
  /\ sleeping = TRUE
  /\ \E i \in Ingredients :
       /\ sleeping' = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
       /\ UNCHANGED offer
  /\ \E o \in Offers : offer' = o

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(StartSmoking)
  /\ WF_vars(StopSmoking)

====