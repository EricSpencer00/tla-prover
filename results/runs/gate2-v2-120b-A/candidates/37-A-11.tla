---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Ingredients, \* The set of all ingredients (e.g., {"matches","paper","tobacco"})
    Offers       \* The set of all valid offers (each missing exactly one ingredient)

\* ----------------------------------------------------------------------
\* State variables
\*   smokers: a function mapping each ingredient to a Boolean indicating
\*            whether the smoker who owns that ingredient is currently smoking.
\*   offer  : the current offer on the table; either a subset of Ingredients
\*            (missing exactly one ingredient) or the empty set (meaning a
\*            smoker is currently smoking).
\* ----------------------------------------------------------------------
VARIABLES smokers, offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllSmokers == { i \in Ingredients : smokers[i] }

\* The set of all subsets of Ingredients that miss exactly one ingredient
\* (this is used for type checking; the actual set is given by the constant
\*  Offers in the .cfg file).
ValidOffers == { s \in SUBSET Ingredients : Cardinality(s) = Cardinality(Ingredients) - 1 }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ i \notin offer                \* i is the missing ingredient
          /\ smokers[i] = FALSE           \* that smoker is not already smoking
          /\ smokers' = [smokers EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smokers[i] = TRUE
          /\ smokers' = [smokers EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smokers, offer>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (not the safety property itself)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in SUBSET Ingredients

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking at any time
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : smokers[i] }) <= 1

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
THEOREM SpecIsSpec == TRUE   \* dummy theorem to expose Spec name to the cfg

====