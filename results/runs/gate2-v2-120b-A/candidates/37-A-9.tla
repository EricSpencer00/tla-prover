---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS Ingredients, Offers

\* ----------------------------------------------------------------------
\* Derived constant: the set of all valid offers (subsets missing exactly one ingredient)
\* ----------------------------------------------------------------------
AllOffers == { S \in SUBSET Ingredients : Cardinality(S) = Cardinality(Ingredients) - 1 }

\* ----------------------------------------------------------------------
\* Variables
\*   Smokers : [Ingredients -> BOOLEAN]   \* true iff the smoker with that
\*                                         ingredient is currently smoking
\*   Offer   : SUBSET Ingredients          \* current offer on the table;
\*                                         \* empty set means a smoker is smoking
\* ----------------------------------------------------------------------
VARIABLES Smokers, Offer

\* ----------------------------------------------------------------------
\* Type invariant (used as TypeOK)
\* ----------------------------------------------------------------------
TypeOK == 
    /\ Smokers \in [Ingredients -> BOOLEAN]
    /\ (Offer = {} \/ Offer \in AllOffers)

\* ----------------------------------------------------------------------
\* Derived predicate: which smoker (if any) is currently smoking
\* ----------------------------------------------------------------------
SmokingSmokers == { i \in Ingredients : Smokers[i] }

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking at any time
\* ----------------------------------------------------------------------
AtMostOne == Cardinality(SmokingSmokers) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\*   - No smoker is smoking
\*   - The dealer places a nondeterministic valid offer
\* ----------------------------------------------------------------------
Init ==
    /\ Smokers = [i \in Ingredients |-> FALSE]
    /\ Offer \in AllOffers

\* ----------------------------------------------------------------------
\* Action: a smoker whose ingredient completes the set begins smoking
\* Preconditions:
\*   - Offer is non‑empty (i.e., a valid offer)
\*   - Exactly one ingredient i is missing from Offer
\*   - The smoker holding i starts smoking
\* Effects:
\*   - Offer becomes empty (indicating a smoker is now smoking)
\*   - That smoker's flag becomes TRUE
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer # {}
    /\ LET missing == Ingredients \ Offer IN
       /\ Cardinality(missing) = 1
       /\ \E i \in missing :
            /\ Smokers[i] = FALSE
            /\ Smokers' = [Smokers EXCEPT ![i] = TRUE]
    /\ Offer' = {}

\* ----------------------------------------------------------------------
\* Action: the currently smoking smoker stops and the dealer places a new offer
\* Preconditions:
\*   - Offer is empty (meaning a smoker is smoking)
\*   - Exactly one smoker is currently smoking
\* Effects:
\*   - That smoker's flag becomes FALSE
\*   - Offer becomes a new nondeterministic valid offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ Offer = {}
    /\ Cardinality(SmokingSmokers) = 1
    /\ \E i \in SmokingSmokers :
         /\ Smokers[i] = TRUE
         /\ Smokers' = [Smokers EXCEPT ![i] = FALSE]
    /\ Offer' \in AllOffers

\* ----------------------------------------------------------------------
\* Stuttering step to satisfy weak fairness when no other action is enabled
\* ----------------------------------------------------------------------
Stutter ==
    /\ UNCHANGED << Smokers, Offer >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == 
    \/ StartSmoking
    \/ StopSmoking
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification (the formula required by the .cfg file)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Smokers, Offer>>

\* ----------------------------------------------------------------------
\* The module's default theorem (optional, but keeps TLC happy)
\* ----------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ AtMostOne)

====