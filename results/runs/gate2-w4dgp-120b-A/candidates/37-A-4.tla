---- MODULE CigaretteSmokers ----
\* A model of the classic cigarette smokers problem. A dealer puts down a combination
\* of ingredients on the table; each smoker holds an infinite supply of exactly one
\* ingredient and can smoke only when the dealer's offer, combined with what they
\* already have, covers the full set. At most one smoker smokes at a time, and the
\* dealer waits for the current smoker to finish before placing a new offer.
EXTENDS Naturals

CONSTANTS Ingredients, Offers

ASSUME Ingredients = {matches, paper, tobacco}
ASSUME Offers = {{matches, paper}, {matches, tobacco}, {paper, tobacco}}

VARIABLES smoking, offer

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

\* Coherence: an offer is present exactly when no smoker is smoking.
OfferConsistent == IF offer = {} THEN \E i \in Ingredients : smoking[i] ELSE TRUE

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

\* A smoker may begin only when their own ingredient, together with the dealer's
\* offer, completes the full set.
CanSmoke(i) == offer # {} /\ ~smoking[i] /\ offer \cup {i} = Ingredients

StartSmoking(i) ==
  /\ CanSmoke(i)
  /\ \A j \in Ingredients : ~smoking[j]
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking(i) ==
  /\ smoking[i]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

\* Weak fairness on the next-state relation ensures the system keeps making
\* progress (smokers keep getting a turn to smoke).
Spec == Init /\ [][Next]_<<smoking, offer>> /\ WF_vars(StopSmoking(matches))
          /\ WF_vars(StopSmoking(paper)) /\ WF_vars(StopSmoking(tobacco))

\* Safety: at most one smoker is smoking at any moment.
AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====