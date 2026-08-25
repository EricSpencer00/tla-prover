---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

\* Type invariant: Smoking is a function from Ingredients to BOOLEAN,
\* and Offer is either a valid offer or the empty set (meaning a smoker is smoking).
TypeOK ==
  /\ Smoking \in [Ingredients -> BOOLEAN]
  /\ (Offer \in Offers \/ Offer = {})

\* Initial state: no smoker is smoking and the dealer places a nondeterministic valid offer.
Init ==
  /\ Smoking = [i \in Ingredients |-> FALSE]
  /\ Offer \in Offers

\* Helper to compute the ingredient missing from an offer.
MissingIngredient(offer) == Ingredients \ offer

\* A smoker whose ingredient completes the set starts smoking; the offer is cleared.
Start ==
  /\ Offer \in Offers
  /\ LET missing == MissingIngredient(Offer) IN
       /\ Cardinality(missing) = 1
       /\ Smoking' = [i \in Ingredients |-> IF i \in missing THEN TRUE ELSE FALSE]
       /\ Offer' = {}

\* The currently smoking smoker stops; the dealer places a new offer.
Stop ==
  /\ Offer = {}
  /\ \E i \in Ingredients : Smoking[i] = TRUE
  /\ Smoking' = [j \in Ingredients |-> FALSE]
  /\ Offer' \in Offers

\* Next-state relation.
Next == \/ Start \/ Stop

\* Specification with weak fairness on Next.
Spec == Init /\ [][Next]_<<Smoking, Offer>> /\ WF_<<Smoking, Offer>>(Next)

\* Safety invariant: at most one smoker is smoking.
AtMostOne == Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

====