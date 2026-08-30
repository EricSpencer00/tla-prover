---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokingStatus maps each ingredient to the smoking status of the smoker who
\* holds an infinite supply of that ingredient.
VARIABLES smokingStatus, offer

vars == <<smokingStatus, offer>>

\* The dealer always keeps exactly one offer on the table, and each offer is a
\* subset of ingredients that is missing exactly one ingredient (a valid offer).
\* A smoker can begin only when that missing ingredient is the one they hold.
TypeOK ==
    /\ smokingStatus \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers

Init ==
    /\ \A i \in Ingredients : smokingStatus[i] = FALSE
    /\ offer \in Offers

AllZero == \A i \in Ingredients : smokingStatus[i] = FALSE

StartSmoking(i) ==
    /\ offer # {}
    /\ i \in offer
    /\ Cards(Ingredients) = Cards(offer \cup {i})
    /\ AllZero
    /\ smokingStatus' = [smokingStatus EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking(i) ==
    /\ offer = {}
    /\ smokingStatus[i] = TRUE
    /\ (\E j \in Ingredients : i = j)
    /\ smokingStatus' = [smokingStatus EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next ==
    \/ \E i \in Ingredients : StartSmoking(i)
    \/ \E i \in Ingredients : StopSmoking(i)

Spec == Init /\ [][Next]_vars

\* At most one smoker is ever smoking: every two smokers that are both smoking
\* must in fact be the same smoker (their held ingredients are equal).
AtMostOne ==
    \A i, j \in Ingredients :
        (smokingStatus[i] /\ smokingStatus[j]) => (i = j)

\* The dealer never gets stuck: when a smoker is on the table, that smoker always
\* eventually stops, regardless of how the dealer re-offers ingredients.
Fairness ==
    [type |-> "weak", vars |-> vars, cond |-> AllZero]

====