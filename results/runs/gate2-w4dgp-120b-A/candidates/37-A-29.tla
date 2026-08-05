---- MODULE CigaretteSmokers ----
\* A model of the cigarette smokers problem, originally described by Suhas Patil in 1971.
\* A dealer places a combination of ingredients on a table; smokers who each have an infinite
\* supply of one ingredient see if the dealer's offer, together with their own, lets them
\* smoke. At most one smoker smokes at a time, and the dealer waits for the current smoker
\* to finish before placing a new offer.
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* smoking[i] says whether the smoker with an infinite supply of ingredient i is
\* currently smoking. The offer is either a non-empty subset of Ingredients missing
\* exactly one ingredient, or empty (meaning a smoker is in the middle of smoking).
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ sleeping == {}
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

\* The dealer places an offer missing exactly one ingredient; a smoker whose
\* ingredient completes the full set begins smoking and the offer is cleared.
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ \A j \in Ingredients : j # i => j \in offer
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* When the offer is empty (someone is smoking), that smoker stops and the dealer
\* places a new offer, chosen nondeterministically from the full set of offers.
StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ \E o \in Offers : offer' = o
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]

Next_ == StartSmoking \/ StopSmoking

ByHand == StartSmoking

Spec == Init /\ [][Next]_vars /\ WF_vars(ByHand)

\* At most one smoker is smoking at any given moment.
AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====