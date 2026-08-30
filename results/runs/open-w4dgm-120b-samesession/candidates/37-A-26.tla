---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* smokers[i] is true exactly when the smoker whose infinite supply is
\* ingredient i is currently smoking.
VARIABLES smokers, offer
vars == <<smokers, offer>>

TypeOK ==
  /\ smokers \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

\* The dealer's offer is always the full set of ingredients minus the single
\* missing one, so exactly one smoker can ever be able to light.
OfferOK ==
  /\ (offer = {} \/ Cardinality(offer) = Cardinality(Ingredients) - 1)

Init ==
  /\ smokers = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* Start: exactly one smoker can light from the current offer.
Start ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smokers[i]
       /\ offer \cup {i} = Ingredients
       /\ smokers' = [smokers EXCEPT ![i] = TRUE]
  /\ offer' = {}

Stop ==
  /\ \A i \in Ingredients : smokers[i]
  /\ smokers' = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer' = o

Next == Start \/ Stop

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Stop)

AtMostOne ==
  /\ \A i \in Ingredients : smokers[i] => offer # {}
  /\ \A i, j \in Ingredients : (smokers[i] /\ smokers[j]) => i = j

TypeOKInv == TypeOK /\ OfferOK
====