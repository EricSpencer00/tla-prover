---- MODULE CigaretteSmokers ----
EXTENDS TLC

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ (offer \in Offers) \/ (offer = {})

\* ----------------------------------------------------------------------
\* Initial state: no smoker is smoking, dealer places a nondeterministic offer
\* ----------------------------------------------------------------------
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ i \notin offer                \* the missing ingredient
          /\ smoking[i] = FALSE
          /\ (offer \cup {i}) = Ingredients
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ offer' = {}

\* ----------------------------------------------------------------------
\* Action: the smoking smoker stops, dealer puts a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ offer' \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* State variable tuple (used for stuttering and fairness)
\* ----------------------------------------------------------------------
vars == <<smoking, offer>>

\* ----------------------------------------------------------------------
\* Specification: initial condition, temporal evolution, weak fairness
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => i = j

\* ----------------------------------------------------------------------
\* The invariants to be checked by TLC
\* ----------------------------------------------------------------------
INVARIANT TypeOK
INVARIANT AtMostOne

====