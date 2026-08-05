---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup { {} }

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* The dealer places an offer that is missing exactly one ingredient. A smoker
\* whose own ingredient completes the full set begins smoking.
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
        /\ \A j \in Ingredients : j # i => offer \cup {j} = Ingredients
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

\* When the offer is empty a smoker is currently smoking; that smoker finishes
\* and the dealer places a new offer.
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
        /\ smoking[i]
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' = CHOOSE o \in Offers :
                    \A x \in Ingredients : o \cup {x} = Ingredients

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

\* At most one smoker smokes at any time.
AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => i = j

\* Progress: the system never settles on a terminated state.
WeakFairness == WF_vars(Next)

====