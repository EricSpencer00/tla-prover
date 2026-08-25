---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, Offer

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smokerStatus \in [Ingredients -> BOOLEAN]
    /\ Offer \in (Offers \cup {∅})
    /\ IF Offer = ∅ THEN
          /\ \E! i \in Ingredients : smokerStatus[i] = TRUE
       ELSE
          /\ \A i \in Ingredients : smokerStatus[i] = FALSE

\* ----------------------------------------------------------------------
\* Initial state: no smoker is smoking and the dealer places a valid offer
\* ----------------------------------------------------------------------
Init ==
    /\ smokerStatus = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker whose missing ingredient is offered starts smoking
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer # ∅
    /\ \E i \in Ingredients :
          /\ i \notin Offer               \* the missing ingredient
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = TRUE]
          /\ Offer' = ∅

\* ----------------------------------------------------------------------
\* Action: the currently smoking smoker stops and the dealer offers anew
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ Offer = ∅
    /\ \E i \in Ingredients :
          /\ smokerStatus[i] = TRUE
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

\* ----------------------------------------------------------------------
\* Next‑state relation
\* ----------------------------------------------------------------------
Next ==
    StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Tuple of all variables (used for stuttering and fairness)
\* ----------------------------------------------------------------------
vars == <<smokerStatus, Offer>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
AtMostOne ==
    \A i, j \in Ingredients :
        (smokerStatus[i] /\ smokerStatus[j]) => i = j

=============================================================================