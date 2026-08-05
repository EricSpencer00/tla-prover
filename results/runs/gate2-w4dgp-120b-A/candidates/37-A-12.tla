---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

Ingredient == CHOOSE x \in Ingredients : TRUE

NoOffer == {}

TypeOK ==
    /\ offer \subseteq Ingredients
    /\ sleeping \in BOOLEAN
    /\ \A i \in Ingredients : smoking[i] \in BOOLEAN
    /\ (sleeping => (offer = NoOffer \/ (offer = Ingredients \ {Ingredient})))

InitOk ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ sleeping = FALSE
    /\ offer \in Offers

Start ==
    /\ ~sleeping
    /\ offer # NoOffer
    /\ \E i \in Ingredients :
        /\ offer \cup {i} = Ingredients
        /\ sleeping' = TRUE
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = NoOffer

Stop ==
    /\ sleeping
    /\ sleeping' = FALSE
    /\ smoking' = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers :
        /\ o # NoOffer
        /\ offer' = o

Next == Start \/ Stop

Spec == InitOk /\ [][Next]_vars

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

====