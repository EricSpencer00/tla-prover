---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* A smoker is identified by the single ingredient it has an infinite supply of.
\* The dealer's offer is always missing exactly one ingredient, and a smoker
\* can smoke only when its own ingredient completes the full set.
Complete == Ingredients

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in SUBSET Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in offer :
       /\ smoking[i] = FALSE
       /\ \A j \in Ingredients : j \notin offer => j = i
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

AtMostOne ==
  Cardinality({i \in Ingredients : smoking[i] = TRUE}) <= 1

Spec == Init /\ [][Next]_vars

====