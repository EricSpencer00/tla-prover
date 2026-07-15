---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT Ingredients
CONSTANT Offers

\* ----------------------------------------------------------------------
\* Derived constant: the full set of ingredients (for readability)
\* ----------------------------------------------------------------------
FullSet == Ingredients

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES smoking, currentOffer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of smokers is identified with the set of ingredients, each smoker
\* possessing the corresponding ingredient.
Smokers == Ingredients

\* The set of valid offers (must be supplied by the .cfg, but we also define
\* it in terms of Ingredients for convenience).  Each offer is a subset that
\* is missing exactly one ingredient.
ValidOffers == { o \in SUBSET Ingredients :
                    Cardinality o = Cardinality Ingredients - 1 }

\* Ensure the constant Offers is indeed a subset of ValidOffers.
\* (The .cfg can override this, but the invariant will catch mis‑configuration.)
OffersSubsetValid == Offers \subseteq ValidOffers

\* ----------------------------------------------------------------------
\* Type correctness predicate (used for the TypeOK invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Smokers -> BOOLEAN]
    /\ currentOffer \in (Offers \cup {∅})

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ smoking = [s \in Smokers |-> FALSE]
    /\ currentOffer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ currentOffer # ∅
    /\ \E s \in Smokers :
          /\ ~smoking[s]
          /\ s \notin currentOffer               \* s is the missing ingredient
          /\ smoking' = [smoking EXCEPT ![s] = TRUE]
          /\ currentOffer' = ∅

StopSmoking ==
    /\ currentOffer = ∅
    /\ \E s \in Smokers :
          /\ smoking[s]                         \* exactly one smoker is smoking
          /\ smoking' = [smoking EXCEPT ![s] = FALSE]
          /\ currentOffer' \in Offers

\* No‑op action to allow stuttering steps (required for weak fairness)
Stutter ==
    /\ UNCHANGED << smoking, currentOffer >>

\* ----------------------------------------------------------------------
\* Next‑state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking \/ Stutter

\* ----------------------------------------------------------------------
\* Specification (used by the .cfg as the top‑level formula)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smoking, currentOffer>>

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking at any time
\* ----------------------------------------------------------------------
AtMostOne == Cardinality { s \in Smokers : smoking[s] } <= 1

=============================================================================