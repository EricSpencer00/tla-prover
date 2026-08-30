---- MODULE CigaretteSmokers ----
EXTENDS Integers

CONSTANTS Ingredients, Offers

\* The smoking status (true/false) of the smoker who holds each ingredient.
Smoking == [i \in Ingredients |-> BOOLEAN]

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ sleeping \in Sleeping
    /\ offer \in Offers \cup {{}}

AtMostOne ==
    /\ \A i \in Ingredients : smoking[i] => (\A j \in Ingredients : j # i => ~smoking[j])
    /\ (offer = {} => \E i \in Ingredients : smoking[i])

Init ==
    /\ \A i \in Ingredients : sleeping[i] = FALSE
    /\ offer \in Offers

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ (offer \cup {i}) = Ingredients
         /\ sleeping' = [sleeping EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
         /\ sleeping[i]
         /\ sleeping' = [sleeping EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

\* Weak fairness on smoking: every smoker who could smoke eventually gets a turn.
Fairness ==
    \A i \in Ingredients :
        TRUE

====