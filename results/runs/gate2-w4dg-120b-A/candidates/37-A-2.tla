---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* A smoker is identified by the unique ingredient it holds an infinite
\* supply of, so smoking maps each ingredient to a Boolean rather than
\* naming the smokers directly.
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in SUBSET Ingredients

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* A smoker may begin only when the dealer's offer, combined with
\* that smoker's own ingredient, supplies the complete set.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ offer \cup {i} = Ingredients
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

\* At most one smoker is ever smoking at a time.
AtMostOne ==
  \A i, j \in Ingredients :
    (smoking[i] /\ smoking[j]) => i = j

Spec == Init /\ [][Next]_vars
  /\ WF_vars(StartSmoking)
  /\ WF_vars(StopSmoking)

====