---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients) \cup {{}}

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers :
        /\ o # {}
        /\ \A i \in Ingredients : Cardinality(o) = Cardinality(Ingredients) - 1
        /\ offer = o

SomeSmoking == \E i \in Ingredients : smoking[i]

StartSmoke(i) ==
    /\ offer # {}
    /\ Cardinality(offer) = Cardinality(Ingredients) - 1
    /\ ~SomeSmoking
    /\ offer \cup {i} = Ingredients
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoke(i) ==
    /\ smoking[i]
    /\ sleeping('') = {}
    /\ sleeping' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers :
        /\ o # {}
        /\ \A j \in Ingredients : Cardinality(o) = Cardinality(Ingredients) - 1
        /\ offer' = o

Next ==
    \E i \in Ingredients :
        \/ StartSmoke(i)
        \/ StopSmoke(i)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A i \in Ingredients : WF_vars(StartSmoke(i))
    /\ \A i \in Ingredients : WF_vars(StopSmoke(i))

AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j

====