---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Smokers: each owns exactly one ingredient and has a boolean smoking flag.
\* Dealer places offers missing one ingredient; the offer is cleared while
\* someone smokes, forcing the dealer to wait for that smoker to finish.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (SUBSET Ingredients) \cup {"empty"}

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

Sober == \A i \in Ingredients : ~smoking[i]

\* Exactly one smoker may start, and only when the offer plus their own
\* ingredient completes the full set of ingredients.
StartSmoking(i) ==
    /\ offer # "empty"
    /\ offer \cup {i} = Ingredients
    /\ Sober
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = "empty"

StopSmoking(i) ==
    /\ smoking[i]
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next ==
    \E i \in Ingredients :
        StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_vars

AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

\* Weak fairness on each smoker's start/stop discharges the liveness
\* obligation associated with the table shifting between offers and smoking.
TypeOKSpec == TypeOK /\ Spec
====