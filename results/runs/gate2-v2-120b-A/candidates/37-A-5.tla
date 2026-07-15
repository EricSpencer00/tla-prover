---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, TLC

CONSTANT Ingredients, Offers

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES smoking, table

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllIngredients == Ingredients

\* An offer is a subset of Ingredients that is missing exactly one ingredient.
ValidOffer(o) == o \in Offers /\ Cardinality(o) = Cardinality(Ingredients) - 1

\* The set of all valid offers (derived from the constant set Ingredients)
ValidOffers == { o \in SUBSET Ingredients : Cardinality(o) = Cardinality(Ingredients) - 1 }

\* The ingredient missing from an offer
MissingIngredient(o) == CHOOSE i \in Ingredients : i \notin o

\* The set of smokers (one per ingredient)
Smokers == Ingredients

\* ----------------------------------------------------------------------
\* Type invariant (helps TLC, but not the safety property)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Smokers -> BOOLEAN]
    /\ table \in SUBSET Ingredients
    /\ (table = {} => \E i \in Smokers : smoking[i] = TRUE)   \* if no offer, exactly one smoker may be smoking
    /\ (table # {} => \A i \in Smokers : ~smoking[i])          \* if an offer is present, no one is smoking

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne == Cardinality({ i \in Smokers : smoking[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ smoking = [i \in Smokers |-> FALSE]
    /\ table \in Offers   \* nondeterministically choose a valid offer

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ table # {}                                   \* an offer is present
    /\ \E i \in Smokers :
          /\ MissingIngredient(table) = i          \* i's ingredient completes the set
          /\ smoking[i] = FALSE
          /\ table' = {}
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ UNCHANGED << >>

StopSmoking ==
    /\ table = {}                                   \* no offer, someone is smoking
    /\ \E i \in Smokers :
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ table' \in Offers
    /\ UNCHANGED << >>

Next ==
    \/ StartSmoking
    \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smoking, table>>

\* ----------------------------------------------------------------------
\* Theorems / properties (the .cfg will use SPECIFICATION Spec)
\* ----------------------------------------------------------------------
=============================================================================