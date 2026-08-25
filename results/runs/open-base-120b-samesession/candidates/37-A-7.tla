---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Smokers, Offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all possible valid offers (subsets missing exactly one ingredient)
ASSUME OffersDef ==
    \A o \in Offers :
        /\ o \subseteq Ingredients
        /\ Cardinality(o) = Cardinality(Ingredients) - 1

\* The set of variables bundled together (used for stuttering and fairness)
Vars == <<Smokers, Offer>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Smokers \in [Ingredients -> BOOLEAN]
    /\ Offer \in Offers \cup { {} }

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : Smokers[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Smokers = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer # {}                                   \* an offer is present
    /\ \E i \in Ingredients :
          /\ i \notin Offer                         \* the missing ingredient
          /\ Smokers[i] = FALSE                     \* not already smoking
          /\ Smokers' = [Smokers EXCEPT ![i] = TRUE]
    /\ Offer' = {}

StopSmoking ==
    /\ Offer = {}                                    \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ Smokers[i] = TRUE
          /\ Smokers' = [Smokers EXCEPT ![i] = FALSE]
    /\ Offer' \in Offers

Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

\* ----------------------------------------------------------------------
\* The invariants that will be checked by TLC
\* ----------------------------------------------------------------------
\* (they are exported simply by being named)
\* TypeOK and AtMostOne are already defined above.

====