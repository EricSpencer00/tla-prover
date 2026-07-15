---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

\*--------------------
\* Constants (to be instantiated in the .cfg)
\*--------------------
CONSTANT Ingredients
CONSTANT Offers

\*--------------------
\* State variables
\*--------------------
VARIABLES Smoking, Offer

\*--------------------
\* Derived definitions
\*--------------------
\* The complete set of ingredients
AllIngredients == Ingredients

\* The set of valid offers (must be subsets missing exactly one ingredient)
ValidOffers == { o \in Offers : Cardinality(o) = Cardinality(AllIngredients) - 1 }

\* The unique smoker (if any) who is currently smoking
CurrentSmoker == 
    IF \E i \in Ingredients : Smoking[i] 
        THEN CHOOSE i \in Ingredients : Smoking[i] 
        ELSE NULL

\*--------------------
\* Initial state
\*--------------------
Init ==
    /\ Offer \in ValidOffers
    /\ Smoking = [i \in Ingredients |-> FALSE]

\*--------------------
\* Actions
\*--------------------
StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer'   = {}
          /\ i \notin Offer
          /\ UNCHANGED << >>  \* no other variables changed
    /\ \A j \in Ingredients : (j # i => Smoking'[j] = Smoking[j])

StopSmoking ==
    /\ Offer = {}
    /\ CurrentSmoker # NULL
    /\ Let s == CurrentSmoker IN
        /\ Smoking' = [Smoking EXCEPT ![s] = FALSE]
        /\ Offer'   \in ValidOffers
        /\ UNCHANGED << >>

Next == StartSmoking \/ StopSmoking

\*--------------------
\* Specification
\*--------------------
Spec == Init /\ [][Next]_<<Smoking, Offer>>

\*--------------------
\* Type correctness invariant (optional but useful)
\*--------------------
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in ValidOffers \/ Offer = {}

\*--------------------
\* Safety invariant: At most one smoker is smoking
\*--------------------
AtMostOne == Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

\*--------------------
\* Liveness property (weak fairness is given in the .cfg, but we expose it here)
\*--------------------
Liveness == <> (Offer = {})

\*--------------------
\* THEOREM (optional, for readability)
\*--------------------
THEOREM Spec => []AtMostOne

====