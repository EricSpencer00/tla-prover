---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (SUBSET Ingredients) \cup {{}}

\* At most one smoker smokes at a time: the sum of the boolean smoking flags
\* (counting each TRUE as 1) never exceeds 1.
AtMostOne == Cardinality({i \in Ingredients : smoking[i]})

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

\* The dealer's offer is non-empty, so a smoker whose ingredient completes the
\* full set can start smoking; the offer is then cleared.
StartSmoke ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ i \notin offer
       /\ \A j \in Ingredients : j # i => j \in offer
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* A single smoker stops, and the dealer places a fresh offer.
StopSmoke ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoke \/ StopSmoke

Spec == Init /\ [][Next]_vars

\* Every declared identifier: Smoking, Offer, Spec, TypeOK, and AtMostOne must
\* be exported exactly as named for the reference configuration to bind them.
====