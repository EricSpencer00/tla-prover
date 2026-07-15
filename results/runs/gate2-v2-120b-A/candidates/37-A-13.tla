---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Ingredients
CONSTANT Offers

VARIABLE smokers   \* mapping each ingredient to a boolean (true = smoking)
VARIABLE offer     \* current offer on the table, a subset of Ingredients

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllIngredients == Ingredients

\* A smoker can smoke iff the current offer together with his own
\* ingredient equals the full set of ingredients.
CanSmoke(i) == 
    /\ i \in Ingredients
    /\ offer # {}
    /\ offer = AllIngredients \ {i}

\* Exactly one smoker is currently smoking
AtMostOne == 
    Cardinality({ i \in Ingredients : smokers[i] }) <= 1

\* Type correctness invariant
TypeOK == 
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in { {} } \cup Offers

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking == 
    \E i \in Ingredients :
        /\ CanSmoke(i)
        /\ smokers' = [smokers EXCEPT ![i] = TRUE]
        /\ offer' = {}

StopSmoking == 
    \E i \in Ingredients :
        /\ smokers[i]
        /\ smokers' = [smokers EXCEPT ![i] = FALSE]
        /\ offer' \in Offers

Next == 
    \/ StartSmoking
    \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smokers, offer>>

\* ----------------------------------------------------------------------
\* Theorem (optional, can be omitted)
\* ----------------------------------------------------------------------
\* THEOREM Spec => []AtMostOne

====