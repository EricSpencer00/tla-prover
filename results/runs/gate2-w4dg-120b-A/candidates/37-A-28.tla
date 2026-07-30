---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumOver(f, S \ {x})

TypeOK ==
    /\ sleeping \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup { {} }

Init ==
    /\ sleeping = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ ~sleeping[i]
         /\ Ingredients = offer \cup {i}
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

AtMostOne ==
    SumOver([i \in Ingredients |-> IF sleeping[i] THEN 1 ELSE 0], Ingredients) <= 1

====