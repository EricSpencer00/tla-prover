---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* Each smoker holds an infinite supply of exactly one ingredient; smoking
\* needs that ingredient plus the dealer's current offer (the other two).
\* smoking is mutually exclusive: no two smokers at once.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients) \cup {"empty"}

AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => (i = j)

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

Start(i) ==
    /\ offer # "empty"
    /\ \E o \in Offers : o = (offer \cup {i})
    /\ \A j \in Ingredients : smoking[j] = FALSE
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = "empty"

Stop(i) ==
    /\ smoking[i] = TRUE
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next ==
    \/ \E i \in Ingredients : Start(i)
    \/ \E i \in Ingredients : Stop(i)

Spec == Init /\ [][Next]_vars
    /\ \A i \in Ingredients : WF_vars(Start(i))
    /\ \A i \in Ingredients : WF_vars(Stop(i))

\* Liveness is driven by the fairness of the per-smoker start and stop actions.
\* Each smoker that can start is eventually started, and each that can stop
\* is eventually stopped, so the system never gets stuck mid-smoke.
====