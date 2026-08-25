---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smokerState, Offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
MissingIngredient(offer) == 
    CHOOSE i \in Ingredients : i \notin offer

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smokerState \in [Ingredients -> BOOLEAN]
    /\ Offer \in Offers \cup { {} }

\* ----------------------------------------------------------------------
\* Safety: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : smokerState[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ smokerState = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer \in Offers                     \* dealer has placed a valid offer
    /\ \E i \in Ingredients :
          i \notin Offer
          /\ smokerState[i] = FALSE
          /\ smokerState' = [smokerState EXCEPT ![i] = TRUE]
          /\ Offer' = {}
    /\ UNCHANGED << >>

StopSmoking ==
    /\ Offer = {}                           \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          smokerState[i] = TRUE
          /\ smokerState' = [smokerState EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers               \* dealer puts a new offer
    /\ UNCHANGED << >>

Next ==
    \/ StartSmoking
    \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<smokerState, Offer>>

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================