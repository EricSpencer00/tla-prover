---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, Offer

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in Offers \/ Offer = {}

\* ----------------------------------------------------------------------
\* Initial state: no one is smoking, dealer places a nondeterministic offer
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
StartSmoking ==
    /\ Offer # {}
    /\ \A i \in Ingredients: ~smoking[i]          \* nobody is smoking yet
    /\ \E i \in Ingredients:
          /\ i \notin Offer                       \* the missing ingredient
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ Offer'   = {}

\* ----------------------------------------------------------------------
\* Action: the current smoker stops and dealer puts a new offer
StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients:
          /\ smoking[i]                           \* the smoker that is active
          /\ \A j \in Ingredients: (smoking[j] => j = i)   \* exactly one
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ Offer'   \in Offers

\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification with weak fairness on the next-state relation
Spec ==
    Init /\ [][Next]_<<smoking, Offer>> /\ WF_<<smoking, Offer>>(Next)

\* ----------------------------------------------------------------------
\* Invariant: at most one smoker may be smoking at any time
AtMostOne ==
    \A i, j \in Ingredients:
        (smoking[i] /\ smoking[j]) => i = j

====