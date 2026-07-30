---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Each smoker is identified by the unique ingredient they have an infinite supply
\* of. Smoking is modelled as a boolean per ingredient/smoker.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* An offer is non-empty when a smoker is free to start: this is the shared
\* resource that limits concurrency to one smoker.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ OfferCompletesSet(i)
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* A single smoker stops, and the dealer refreshes the offer.
StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

OfferCompletesSet(i) == offer \cup {i} = Ingredients

Next == StartSmoking \/ StopSmoking

\* Weak fairness on the next-state relation gives the progress guarantee.
Spec == Init /\ [][Next]_vars
  /\ WF_vars(Next)

AtMostOne ==
  /\ \A i1, i2 \in Ingredients : (smoking[i1] /\ smoking[i2]) => i1 = i2
  /\ \E i \in Ingredients : smoking[i] = TRUE => OfferCompletesSet(i)

====