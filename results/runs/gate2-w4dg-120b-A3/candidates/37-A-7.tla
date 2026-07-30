---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Each smoker holds an infinite supply of exactly one distinct ingredient; the
\* map `smoking` records, per ingredient, whether that smoker is currently smoking.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \subseteq Ingredients

\* A smoker may start only if its own ingredient, together with the dealer's
\* existing offer, covers the whole set of ingredients.
CanSmoke(i) == offer # {} /\ offer \cup {i} = Ingredients

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

StartSmoke ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ CanSmoke(i)
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoke ==
    /\ offer = {}
    /\ \E i \in Ingredients :
         /\ smoking[i]
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoke \/ StopSmoke

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* At most one smoker is ever smoking at the same time.
AtMostOne ==
    \A i1 \in Ingredients, i2 \in Ingredients :
        (smoking[i1] /\ smoking[i2]) => i1 = i2

====