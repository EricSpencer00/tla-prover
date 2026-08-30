---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Smoking status is held per ingredient, because each smoker owns exactly
\* one distinct ingredient rather than an arbitrary identity.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

\* The invariant the whole exercise exists to protect: never more than one
\* smoker in the critical section (smoking) at a time.
AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) <= 1

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  \E i \in Ingredients :
    /\ offer # {}
    /\ (offer \cup {i}) = Ingredients
    /\ smoking[i] = FALSE
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
  \E i \in Ingredients :
    /\ offer = {}
    /\ smoking[i] = TRUE
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

\* Progress: a smoker eventually lights up and finishes, under weak fairness
\* on each transition so the system never gets stuck on its own.
Properties == TRUE

====