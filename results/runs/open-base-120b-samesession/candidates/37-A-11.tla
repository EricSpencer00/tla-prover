---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in SUBSET Ingredients

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => i = j

\* ----------------------------------------------------------------------
\* Initial state: no smoker is smoking, dealer places a nondeterministic offer
\* ----------------------------------------------------------------------
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
\* The current offer must be a valid subset missing exactly one ingredient i.
\* That smoker (who holds i) begins smoking and the offer is cleared.
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ offer = Ingredients \ {i}
          /\ ~smoking[i]
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ offer'   = {}

\* ----------------------------------------------------------------------
\* Action: the currently smoking smoker stops and dealer places a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i]
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ offer'   \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \/ StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << smoking, offer >>

Spec == Init /\ [] [Next]_vars

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
\* INVARIANTS
\* (the cfg file will refer to these names)
\* ----------------------------------------------------------------------
\* Note: The cfg file should contain:
\*    SPECIFICATION Spec
\*    INVARIANT TypeOK
\*    INVARIANT AtMostOne
\* ----------------------------------------------------------------------
====