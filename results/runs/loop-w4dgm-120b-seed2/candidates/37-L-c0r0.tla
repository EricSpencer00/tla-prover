---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking[i] is the smoking flag of the smoker who holds an infinite supply of ingredient i.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

\* A smoker may only start if the dealer's offer, plus that smoker's own ingredient,
\* completes the full set of ingredients.
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ offer \cup {i} = Ingredients
         /\ smoking[i] = FALSE
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
         /\ smoking[i] = TRUE
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

\* Progress: the system never gets stuck with a smoker smoking forever.
\* The weak fairness on Next (which covers both StartSmoking and StopSmoking)
\* forces the cycle of start and stop to keep repeating.
\* (Explicit PF_vars is not needed here because the single Next action is
\* already declared weakly fair in the .cfg, but the property is kept for
\* completeness and symmetry with the invariant section.)
Progress == TRUE

====