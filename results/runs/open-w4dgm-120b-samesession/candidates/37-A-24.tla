---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smokers[i] maps each ingredient to the smoker who holds an infinite supply
\* of it; smoking[i] is that smoker's boolean smoking flag.
VARIABLES smokers, smoking, offer

vars == <<smokers, smoking, offer>>

TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients) \union {"Empty"}

Init ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* Exactly one smoker begins: the offer must be non-empty and together with the
\* smoker's own infinite ingredient form the full set.
StartSmoking ==
    /\ offer # "Empty"
    /\ \E i \in Ingredients :
         /\ ~ smoking[i]
         /\ (offer \union {i}) = Ingredients
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = "Empty"
    /\ UNCHANGED <<smokers>>

StopSmoking ==
    /\ offer = "Empty"
    /\ \E i \in Ingredients :
         /\ smoking[i]
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' \in Offers
    /\ UNCHANGED <<smokers>>

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

\* Progress: the system never gets stuck with everybody sleeping and no offer.
StateConstraint ==
    (offer = "Empty") ~> (offer # "Empty")

====