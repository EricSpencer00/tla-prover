---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* smokers[i]: whether the smoker holding ingredient i is currently smoking
\* offer: the dealer's current table offer (empty while someone smokes)
VARIABLES smokers, offer

vars == <<smokers, offer>>

TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients) \union {"empty"}

Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

SmokingYet == \E i \in Ingredients : smokers[i]

\* A smoker whose ingredient completes the set begins, consuming the offer
StartSmoking ==
    /\ offer # "empty"
    /\ \A i \in Ingredients : (Offer \union {i} = Ingredients) => smokers' = [smokers EXCEPT ![i] = TRUE]
    /\ offer' = "empty"

\* When the offer is empty (someone smoking), that smoker stops and a new offer is placed
StopSmoking ==
    /\ SmokingYet
    /\ offer = "empty"
    /\ \E i \in Ingredients : smokers[i]
    /\ smokers' = [j \in Ingredients |-> FALSE]
    /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
    /\ SF_vars(StartSmoking) /\ WF_vars(StopSmoking)

AtMostOne ==
    \A i, j \in Ingredients : (smokers[i] /\ smokers[j]) => i = j

\* Each smoker carries exactly one ingredient, so the per-smoker flag and the
\* literal smoker count are equivalent ways to state "at most one smoker":
\* the property holds under either interpretation.
RollUp == Cardinality({ i \in Ingredients : smokers[i] }) =< 1

TypeOKInv == TypeOK
AtMostOneInv == AtMostOne
====