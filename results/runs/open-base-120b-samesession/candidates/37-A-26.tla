---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, offer

\* ----------------------------------------------------------------------
\* Type invariant: the smoker status maps each ingredient to a Boolean,
\* and the offer is either empty (someone is smoking) or a valid offer.
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smokerStatus \in [Ingredients -> BOOLEAN]
    /\ (offer = {} \/ offer \in Offers)

\* ----------------------------------------------------------------------
\* At most one smoker may be smoking at any moment.
\* ----------------------------------------------------------------------
AtMostOne ==
    \A i, j \in Ingredients :
        (smokerStatus[i] /\ smokerStatus[j]) => i = j

\* ----------------------------------------------------------------------
\* Initial state: no one is smoking and the dealer places a nondeterministic
\* valid offer.
\* ----------------------------------------------------------------------
Init ==
    /\ smokerStatus = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* The ingredient missing from the current (non‑empty) offer.
\* ----------------------------------------------------------------------
MissingIngredient ==
    IF offer = {} THEN {} ELSE Ingredients \ offer

\* ----------------------------------------------------------------------
\* StartSmoking: the dealer has placed an offer, exactly the smoker whose
\* ingredient is missing starts smoking, and the offer becomes empty.
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}                         \* there is an offer on the table
    /\ \A i \in Ingredients : smokerStatus[i] = FALSE   \* nobody currently smoking
    /\ \E i \in Ingredients :
          /\ i \notin offer               \* i is the missing ingredient
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = TRUE]
          /\ offer' = {}

\* ----------------------------------------------------------------------
\* StopSmoking: a smoker finishes, the dealer puts a new offer on the table.
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ offer = {}                         \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ smokerStatus[i] = TRUE
          /\ \A j \in Ingredients : (smokerStatus[j] = TRUE) => j = i
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
          /\ offer' \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation.
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* A tuple of all variables, used for the stuttering step.
\* ----------------------------------------------------------------------
vars == <<smokerStatus, offer>>

\* ----------------------------------------------------------------------
\* Specification: initial condition and always‑next.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

====