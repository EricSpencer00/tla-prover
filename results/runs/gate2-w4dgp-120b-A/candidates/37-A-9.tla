---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in {Offers} \cup {{}}

AtMostOne ==
    \A a, b \in Ingredients : (smoking[a] /\ smoking[b]) => a = b

Init ==
    /\ smoking = [a \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

Next ==
    \/ (\E a \in Ingredients :
            /\ offer # {}
            /\ offer = (Ingredients \ {a})
            /\ smoking[a] = FALSE
            /\ smoking' = [smoking EXCEPT ![a] = TRUE]
            /\ offer' = {})
    \/ (\E o \in Offers :
            /\ offer = {}
            /\ \E a \in Ingredients : smoking[a] = TRUE
            /\ smoking' = [a \in Ingredients |-> FALSE]
            /\ offer' = o)

Spec == Init /\ [][Next]_vars

====