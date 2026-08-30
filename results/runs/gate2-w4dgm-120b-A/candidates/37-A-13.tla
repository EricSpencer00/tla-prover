---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

\* A smoker smokes when the dealer's offered ingredients, plus the
\* smoker's own infinite supply, make a complete set.  The dealer waits.
CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \subseteq Ingredients

\* Exactly one smoker smokes at a time: the smokers are mutually exclusive.
AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ \E o \in Offers : offer = o

Start == \E i \in Ingredients :
    /\ offer # {}
    /\ offer \cup {i} = Ingredients
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

Stop == \E i \in Ingredients :
    /\ offer = {}
    /\ smoking[i]
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == Start \/ Stop

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Stop) /\ WF_vars(Start)

\* smoking's domain is exactly the smokers, and offer is always a valid offer.
DomainTypeOK ==
    /\ \A i \in Ingredients : smoking[i] \in BOOLEAN
    /\ offer \in (Offers \cup {Offers})

====