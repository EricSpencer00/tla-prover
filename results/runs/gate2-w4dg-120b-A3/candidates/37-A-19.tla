---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* An offer is valid when it contains every ingredient except exactly one.
OfferValid(o) == o \in Offers /\ Cardinality(Ingredients \ o) = 1

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ /\ OfferValid(offer)
     \/ offer = {}

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o /\ OfferValid(o)

\* The smoker whose own ingredient completes the full set begins smoking.
StartSmoking(i) ==
  /\ offer # {}
  /\ \A j \in Ingredients : (~smoking[j]) /\ ((i \in offer) \/ (j \in offer))
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* After smoking, the dealer puts down a fresh, nondeterministic valid offer.
StopSmoking(i) ==
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o /\ OfferValid(o)

Next ==
  \/ \E i \in Ingredients : StartSmoking(i)
  \/ \E i \in Ingredients : StopSmoking(i)

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A i \in Ingredients, j \in Ingredients :
    (smoking[i] /\ smoking[j]) => i = j

====