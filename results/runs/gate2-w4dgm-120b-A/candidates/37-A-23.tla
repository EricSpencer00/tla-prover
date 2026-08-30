---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

SMOKING == {g \in Ingredients : smoking[g]}
FullSet == Ingredients

TypeOK ==
    /\ sleeping \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

CompleteSet(f, g) == f \cup {g}
AtMostOne == \A a, b \in SMOKING : a = b

Init ==
    /\ \E g \in Ingredients : sleeping = [h \in Ingredients |-> h = g]
    /\ \E o \in Offers : offer = o

StartSmoking(g) ==
    /\ offer # {}
    /\ CompleteSet(offer, g) = FullSet
    /\ sleeping[g]
    /\ sleeping' = [sleeping EXCEPT ![g] = FALSE]
    /\ offer' = {}

StopSmoking(g) ==
    /\ offer = {}
    /\ ~sleeping[g]
    /\ \E e \in Ingredients : sleeping[e]
    /\ sleeping' = [sleeping EXCEPT ![g] = TRUE]
    /\ \E o \in Offers : offer' = o

Next ==
    \E g \in Ingredients : StartSmoking(g) \/ StopSmoking(g)

Spec == Init /\ [][Next]_vars

TypeOK == TypeOK
AtMostOne == AtMostOne
====