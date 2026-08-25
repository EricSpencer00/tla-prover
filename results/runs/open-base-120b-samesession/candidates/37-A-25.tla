---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Ingredients, \* set of all ingredients (e.g., {matches, paper, tobacco})
    Offers       \* set of subsets of Ingredients, each missing exactly one ingredient

VARIABLES
    Smoking,     \* [Ingredients -> BOOLEAN] : true iff the smoker owning that ingredient is smoking
    Offer        \* subset of Ingredients currently on the table ({} when a smoker is smoking)

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer \in Offers) \/ (Offer = {})

\* ----------------------------------------------------------------------
\* At most one smoker may be smoking
AtMostOne ==
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial state: no one is smoking, dealer places a nondeterministic valid offer
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
StartSmoking ==
    /\ Offer \in Offers                \* a non‑empty valid offer is on the table
    /\ \A i \in Ingredients : ~Smoking[i]   \* no smoker is currently smoking
    LET missing == Ingredients \ Offer IN
        /\ missing \in Ingredients    \* exactly one ingredient is missing
        /\ Smoking' = [Smoking EXCEPT ![missing] = TRUE]
        /\ Offer'   = {}
    IN  TRUE

\* ----------------------------------------------------------------------
\* Action: the current smoker stops and dealer puts a new offer
StopSmoking ==
    /\ Offer = {}                     \* a smoker is currently smoking
    /\ Cardinality({ i \in Ingredients : Smoking[i] }) = 1
    /\ Smoking' = [i \in Ingredients |-> FALSE]
    /\ Offer' \in Offers

\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Tuple of all variables for priming and fairness
vars == << Smoking, Offer >>

\* ----------------------------------------------------------------------
\* Specification: init, always-next, and weak fairness of Next
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================