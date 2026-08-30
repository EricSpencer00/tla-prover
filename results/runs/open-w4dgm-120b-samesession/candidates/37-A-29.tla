---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

\* smokes[i] is the smoking status of the smoker whose infinite supply is
\* ingredient i. offer is the subset on the table, or empty while a smoker
\* smokes; exactly one smoker smokes at a time.
VARIABLES smokes, offer

vars == <<smokes, offer>>

TypeOK ==
    /\ smokes \in [Ingredients -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients) \cup {"none"}

Init ==
    /\ smokes = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

StartSmoking(i) ==
    /\ offer # "none"
    /\ ~ smokes[i]
    /\ (offer \cup {i}) = Ingredients
    /\ smokes' = [smokes EXCEPT ![i] = TRUE]
    /\ offer' = "none"

StopSmoking(i) ==
    /\ smokes[i]
    /\ smokes' = [smokes EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next ==
    \/ \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_vars

AtMostOne == \A i \in Ingredients : smokes[i] => (\A j \in Ingredients : j # i => ~ smokes[j])

\* Progress: the system never gets stuck with someone smoking forever.
Fairness == WF_vars([i \in Ingredients] : StopSmoking(i))

====