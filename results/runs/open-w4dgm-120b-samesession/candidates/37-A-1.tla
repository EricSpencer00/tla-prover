---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* A smoker possesses an infinite supply of exactly one ingredient; the
\* smoking map is keyed by that ingredient, and the offer is either a subset
\* of ingredients or empty (meaning a smoker is currently smoking).
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* A smoker may start only if the offer covers every other ingredient.
CanSmoke(i) == offer # {} /\ ~smoking[i] /\ (Cardinality(offer \cup {i}) = Cardinality(Ingredients))

StartSmoking ==
  \E i \in Ingredients :
    /\ CanSmoke(i)
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
  \E i \in Ingredients :
    /\ smoking[i]
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
  /\ WF_vars(StopSmoking)

\* Safety: smoking flags stay disjoint so two smokers never run at once.
AtMostOne ==
  \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

\* Trivial shape check: every offer leaves out exactly one ingredient.
TypeOKOffers == \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

====