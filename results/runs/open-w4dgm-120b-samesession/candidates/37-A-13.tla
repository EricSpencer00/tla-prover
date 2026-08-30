---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* smoking: which smoker (identified by the ingredient it hoards) is currently lighting
\* offer: the dealer's current placement, or empty while somebody smokes.
Variables smoking, offer

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup { {} }

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : o # {} /\ Cardinality(o) = Cardinality(Ingredients) - 1 /\ offer = o

CanSmoke(i) ==
    /\ offer # {}
    /\ Ingredients = offer \cup {i}
    /\ \A j \in Ingredients : ~ smoking[j]

StartSmoking(i) ==
    /\ CanSmoke(i)
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking(i) ==
    /\ smoking[i]
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : o # {} /\ Cardinality(o) = Cardinality(Ingredients) - 1 /\ offer' = o

Next ==
    \/ \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec == Init /\ [][Next]_<<smoking, offer>>

AtMostOne ==
    Cardinality({i \in Ingredients : smoking[i]}) <= 1

====