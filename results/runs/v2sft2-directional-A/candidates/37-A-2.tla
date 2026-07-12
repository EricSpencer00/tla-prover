---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Ingredients, Offers

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES smokers, offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Each smoker is identified by the ingredient they possess
\* smokers : Ingredient -> BOOLEAN
\* offer    : SUBSET Ingredients | {} (empty indicates someone is smoking)

\* Type correctness predicate
TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup { {} }

\* Safety invariant: at most one smoker is smoking
AtMostOne ==
    Cardinality({ i \in Ingredients : smokers[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ smokers = [ i \in Ingredients |-> FALSE ]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* Start smoking: a smoker whose ingredient combined with the offer yields all ingredients begins smoking.
StartSmoking ==
    \E i \in Ingredients :
        /\ offer # {}
        /\ !smokers[i]
        /\ Ingredients = offer \cup { i }
        /\ smokers' = [ smokers EXCEPT ![i] = TRUE ]
        /\ offer' = {}

\* Stop smoking: the only smoker currently smoking stops, and the dealer places a new offer.
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients : smokers[i] = TRUE
    /\ LET j == ChosenSmoker(\E i \in Ingredients : smokers[i] = TRUE) IN
           /\ smokers' = [ smokers EXCEPT ![j] = FALSE ]
           /\ offer' \in Offers

\* Next-state relation
Next == StartSmoking \/ StopSmoking

\* Specification
Spec ==
    Init /\ [][Next]_<<smokers, offer>>

\* ----------------------------------------------------------------------
\* Theorem (optional) to aid TLC: the set of offers is exactly the set of all
\* subsets of Ingredients missing exactly one element. This is not used in
\* the invariants but helps model-checking if the constant is defined
\* incorrectly.
\* ----------------------------------------------------------------------
ValidOffers ==
    Offers = { s \subseteq Ingredients : Cardinality(s) = Cardinality(Ingredients) - 1 }

\* ----------------------------------------------------------------------
\* The module also defines the weak fairness condition for liveness.
\* ----------------------------------------------------------------------
THEOREM WeakFairness ==
  WF_Always(Next)

====