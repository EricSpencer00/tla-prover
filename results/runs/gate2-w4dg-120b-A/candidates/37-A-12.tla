---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* A smoker is identified by the single ingredient it has an infinite supply of.
VARIABLES smoking, offer

vars == <<smoking, offer>>

\* Each smoker's state is a boolean keyed by the ingredient it holds.
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

Init ==
    /\ smoking = [g \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

\* A smoker may begin only if the dealer's current offer, together with the
\* smoker's own ingredient, yields a complete set.
StartSmoking(g) ==
    /\ smoking[g] = FALSE
    /\ offer # {}
    /\ (offer \cup {g} = Ingredients)
    /\ smoking' = [smoking EXCEPT ![g] = TRUE]
    /\ offer' = {}

StopSmoking(g) ==
    /\ smoking[g] = TRUE
    /\ offer = {}
    /\ smoking' = [smoking EXCEPT ![g] = FALSE]
    /\ \E o \in Offers : offer' = o

Next ==
    \/ \E g \in Ingredients : StartSmoking(g)
    \/ \E g \in Ingredients : StopSmoking(g)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E g \in Ingredients : StartSmoking(g))
    /\ WF_vars(\E g \in Ingredients : StopSmoking(g))

\* The two smokers' actions are mutually exclusive, so the smoking flags form
\* a pairwise-disjoint set of at most one true value.
AtMostOne ==
    \A g1, g2 \in Ingredients :
        (smoking[g1] /\ smoking[g2]) => g1 = g2

====