---- MODULE CigaretteSmokers ----
EXTENDS Integers

CONSTANTS Ingredients, Offers

\* Smoking maps each ingredient to the smoking flag of the smoker who holds
\* an infinite supply of that ingredient. The offer is a subset of
\* Ingredients (missing exactly one) or empty while a smoker is smoking.
VARIABLES Smoking, Offer

TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in (Offers \cup {{} })

Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : Offer = o

\* Exactly one smoker's ingredient completes the full set, so the offer is
\* unambiguous and only one smoker's flag is set to TRUE.
StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
         /\ Offer \cup {i} = Ingredients
         /\ Smoking[i] = FALSE
         /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
    /\ Offer' = {}

StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
         /\ Smoking[i]
         /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : Offer' = o

Next == StartSmoking \/ StopSmoking

\* Progress: the system never gets stuck waiting forever.
Spec == Init /\ [][Next]_<<Smoking, Offer>> /\ WF_vars(Next)

AtMostOne ==
    \A i, j \in Ingredients : (Smoking[i] /\ Smoking[j]) => (i = j)

====