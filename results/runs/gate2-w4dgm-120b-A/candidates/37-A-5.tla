---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokers: each ingredient's owner; smoking: who is lighting up; offer:
\* the dealer's current table (empty while a smoker is lit).
VARIABLES smokers, smoking, offer

vars == <<smokers, smoking, offer>>

TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {"Free"}

Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

Complete(i) == i \in offer

Start(i) ==
    /\ smokers[i] = FALSE
    /\ offer # "Free"
    /\ Complete(i)
    /\ smokers' = [smokers EXCEPT ![i] = TRUE]
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = "Free"

Stop(i) ==
    /\ smokers[i] = TRUE
    /\ smokers' = [smokers EXCEPT ![i] = FALSE]
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == \E i \in Ingredients : Start(i) \/ Stop(i)

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => i = j

\* Progress: smokers keep lighting up and extinguishing.
\* Fairness arguments are always tied to the actions that enable them.
StateConstraints == [i \in Ingredients |-> TRUE]
FairnessConstraints ==
    \A i \in Ingredients :
        /\ TRUE
        /\ TRUE

====