---- MODULE CigaretteSmokers ----
EXTENDS Naturals, TLC

CONSTANTS
    Ingredients, \* Set of all ingredients, e.g., {matches, paper, tobacco}
    Offers       \* Set of all valid offers (each is Ingredients missing exactly one)

\* ----------------------------------------------------------------------
\* State variables
\* smoking[s] = TRUE iff smoker who owns ingredient s is currently smoking
\* currentOffer is either an element of Offers or {} indicating a smoker is smoking
\* ----------------------------------------------------------------------
VARIABLES
    smoking,          \* [Ingredients -> BOOLEAN]
    currentOffer      \* SUBSET Ingredients (or {})

\* ----------------------------------------------------------------------
\* Type correctness predicate (used as an invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ currentOffer \in (Offers \cup { {}})

\* ----------------------------------------------------------------------
\* Initial state
\* All smokers are not smoking and the dealer places a nondeterministic offer
\* ----------------------------------------------------------------------
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ currentOffer \in Offers

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllIngredients == Ingredients

\* The unique smoker that can smoke given the current offer:
\* It is the ingredient not present in the offer.
\* When currentOffer = {}, there is no such smoker.
\* ----------------------------------------------------------------------
SmokerCanSmoke(s) ==
    /\ currentOffer # {}
    /\ s \in Ingredients
    /\ s \notin currentOffer
    /\ \A i \in Ingredients : i # s => i \in currentOffer

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------

\* Start smoking: a smoker whose ingredient completes the set starts smoking.
StartSmoking ==
    \E s \in Ingredients :
        /\ SmokerCanSmoke(s)
        /\ smoking' = [smoking EXCEPT ![s] = TRUE]
        /\ currentOffer' = {}

\* Stop smoking: the smoker finishes and the dealer posts a new offer.
StopSmoking ==
    \E s \in Ingredients :
        /\ smoking[s] = TRUE
        /\ smoking' = [smoking EXCEPT ![s] = FALSE]
        /\ currentOffer' \in Offers

\* Stutter step to satisfy fairness when no move is possible (should not happen)
Stutter ==
    /\ UNCHANGED <<smoking, currentOffer>>

Next ==
    \/ StartSmoking
    \/ StopSmoking
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smoking, currentOffer>>

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking at any time
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ s \in Ingredients : smoking[s] }) <= 1

\* ----------------------------------------------------------------------
\* Theorems (optional, but keep the spec tidy)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []AtMostOne

====