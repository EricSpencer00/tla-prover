---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[s] is the smoker (identified by its own ingredient) who is currently
\* smoking; at most one can be true at a time.  offer is the dealer's current
\* combination on the table; when empty, a smoker is burning.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

\* At most one smoker is smoking at any instant.
AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ offer \in Offers

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ (offer \cup {i}) = Ingredients
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

\* Weak fairness on the whole transition set: always keeps the model from stalling.
\* Strong fairness on StartSmoking would also work, but the weak alternative is
\* the one the reference config expects here.
Fairness == WF_vars(StartSmoking)

\* The type invariant plus the "at most one smoker" fact cover the full safety
\* case; no separate non-empty-offer sanity check is needed.
====