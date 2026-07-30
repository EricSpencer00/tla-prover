---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Smoking[i] is the smoking flag of the smoker who holds an infinite
\* supply of ingredient i. The dealer's offer is on the table when non-empty
\* and cleared to empty while a smoker is smoking.
VARIABLES Smoking, Offer

vars == <<Smoking, Offer>>

TypeOK == /\ Smoking \in [Ingredients -> BOOLEAN]
          /\ Offer \in { {} } \union Offers

Init == /\ Smoking = [i \in Ingredients |-> FALSE]
        /\ Offer \in Offers

\* Start smoking when the offer completes the full set together with this
\* smoker's own ingredient. The offer is cleared once somebody starts.
StartSmoking(i) == /\ Offer # {}
                   /\ \A j \in Ingredients : (j \in Offer \/ j = i)
                   /\ Smoking[i] = FALSE
                   /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
                   /\ Offer' = {}
                   /\ UNCHANGED <<>>

\* Stop smoking: only allowed when nobody sees an offer on the table, i.e.
\* exactly one smoker is currently smoking.
StopSmoking(i) == /\ Offer = {}
                  /\ Smoking[i] = TRUE
                  /\ \A j \in Ingredients : Smoking[j] = FALSE \/ j = i
                  /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
                  /\ Offer' \in Offers
                  /\ UNCHANGED <<>>

Next == \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

\* Only one smoker may ever be smoking; the offer-empty test on StopSmoking
\* is what excludes a second one from starting before the first finishes.
AtMostOne == \A i, j \in Ingredients :
               (Smoking[i] /\ Smoking[j]) => i = j

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in Ingredients : StartSmoking(i))
        /\ WF_vars(\E i \in Ingredients : StopSmoking(i))

====