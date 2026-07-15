---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANT Ingredients, Offers

\* ----------------------------------------------------------------------
\* State variables
\*   smokers : a mapping that records for each ingredient whether the
\*             smoker who owns that ingredient is currently smoking
\*   offer   : the current set of ingredients placed on the table.
\*             It is either empty (meaning a smoker is currently smoking)
\*             or one of the valid offers (a subset missing exactly one
\*             ingredient).
\* ----------------------------------------------------------------------
VARIABLES smokers, offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllIngredients == Ingredients

\* Valid offers are exactly those subsets of Ingredients that miss one
\* ingredient.  The constant Offers must satisfy this property; we also
\* use it to restrict the nondeterministic choice of a new offer.
\* ----------------------------------------------------------------------
IsValidOffer(o) == o \in Offers /\ Cardinality(o) = Cardinality(Ingredients) - 1

\* The smoker that can smoke given the current offer o is the one whose
\* own ingredient is the missing one.
\* ----------------------------------------------------------------------
MissingIngredient(o) == CHOOSE i \in Ingredients : i \notin o

\* The set of ingredients currently held by the smoker who is smoking,
\* i.e., the smoker's own ingredient combined with the offer.  When no
\* one is smoking (offer = {}), this set is empty.
\* ----------------------------------------------------------------------
FullSet == Ingredients

\* ----------------------------------------------------------------------
\* Type correctness predicate (used for the TypeOK invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in (Offers \cup {{}})
    /\ (offer = {} => \E i \in Ingredients : smokers[i] = TRUE)
    /\ (offer # {} => \A i \in Ingredients : smokers[i] = FALSE)

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : smokers[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ LET i == MissingIngredient(offer) IN
       /\ smokers[i] = FALSE
       /\ smokers' = [smokers EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smokers[i] = TRUE
          /\ smokers' = [smokers EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification (temporal formula)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smokers, offer>>

\* ----------------------------------------------------------------------
\* The configuration file will refer to the following identifiers
\*   - Spec          : the temporal specification
\*   - Init, Next   : already defined
\*   - TypeOK, AtMostOne : invariants
\* ----------------------------------------------------------------------
====