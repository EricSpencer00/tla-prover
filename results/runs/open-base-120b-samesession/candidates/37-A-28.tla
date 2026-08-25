---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Ingredients, Offers

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES smoker, offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == <<smoker, offer>>

\* The set of all ingredients
AllIngredients == Ingredients

\* A valid offer is a subset of Ingredients that is missing exactly one
\* ingredient.  The constant Offers must satisfy this property; we state it
\* as an assumption that can be checked in the model.
ASSUME OffersSubset == Offers \subseteq SUBSET Ingredients
ASSUME OfferSizeOK == \A o \in Offers: Cardinality(o) = Cardinality(Ingredients) - 1

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoker \in [Ingredients -> BOOLEAN]
    /\ (offer \in Offers) \/ (offer = {})

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ smoker = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}                         \* there is an offer on the table
    /\ \E i \in Ingredients :
          /\ i \notin offer                \* the missing ingredient
          /\ smoker[i] = FALSE
          /\ smoker' = [smoker EXCEPT ![i] = TRUE]
          /\ offer' = {}
    /\ UNCHANGED <<smoker \ {i}, offer \ {i}>>  \* all other variables unchanged

StopSmoking ==
    /\ offer = {}                         \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ smoker[i] = TRUE
          /\ smoker' = [smoker EXCEPT ![i] = FALSE]
          /\ offer' \in Offers
    /\ UNCHANGED <<smoker \ {i}, offer \ {i}>>  \* all other variables unchanged

Next ==
    \/ StartSmoking
    \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    \A i, j \in Ingredients :
        (smoker[i] /\ smoker[j]) => i = j

====