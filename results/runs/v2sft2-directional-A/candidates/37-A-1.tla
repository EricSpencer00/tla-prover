---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokers, offer

\* smokers is a mapping from each ingredient to a boolean indicating whether the smoker who has that ingredient is currently smoking.

\* offer is either a subset of Ingredients that is a valid offer (missing exactly one ingredient) or the empty set when a smoker is smoking.

\* Type correctness invariant
TypeOK == /\ smokers \in [Ingredients -> BOOLEAN]
          /\ offer \in Offers \cup {{}}

\* At most one smoker may be smoking at any time
AtMostOne == \E a \in Ingredients : smokers[a]

\* Initial state: no smoker is smoking and the dealer places an initial offer.
Init == /\ smokers = [i \in Ingredients |-> FALSE]
        /\ offer \in Offers

\* Actions

\* Start smoking: when the offer is non-empty, exactly one smoker (the one whose ingredient completes the offer) begins smoking and the offer becomes empty.
StartSmoking == 
    \E i \in Ingredients :
        /\ offer \in Offers
        /\ i \notin offer          \* i is the missing ingredient
        /\ offer = Ingredients \ {i}
        /\ smokers[i] = FALSE
        /\ smokers' = [smokers EXCEPT ![i] = TRUE]
        /\ offer' = {}

\* Stop smoking: when the offer is empty, the single currently smoking smoker stops, and the dealer places a new offer chosen nondeterministically.
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients : smokers[i] = TRUE
    /\ smokers' = [i \in Ingredients |-> FALSE]
    /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_<<smokers, offer>>

\* Weak fairness on Next to guarantee liveness
WF_Next == WF_ON Next

====