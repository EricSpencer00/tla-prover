---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* "Smoking" is keyed by the ingredient a smoker infinitely holds; each smoker is
\* identified by the ingredient it owns.
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

\* The dealer places a missing-ingredients offer only while nobody is smoking.
Start ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ i \notin offer
       /\ \A j \in Ingredients : j # i => (~smoking[j])
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* The single smoker finishes and the dealer replaces the offer.
Stop ==
  /\ offer = {}
  /\ \E i \in Ingredients : smoking[i]
  /\ \E o \in Offers :
       /\ o # {}
       /\ \E j \in Ingredients : j \notin o
       /\ offer' = o
  /\ smoking' = [i \in Ingredients |-> FALSE]

Next == Start \/ Stop

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====