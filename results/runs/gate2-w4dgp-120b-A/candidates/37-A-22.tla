---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \subseteq Ingredients

\* At most one smoker smokes at a time: the smoker with an infinite supply
\* of a particular ingredient smokes only when the dealer's offer, together
\* with that ingredient, provides the complete set.
AtMostOne ==
  \A i1, i2 \in Ingredients :
    (smoking[i1] /\ smoking[i2]) => (i1 = i2)

Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

\* The dealer's offer always lacks exactly one ingredient; the smoking
\* smoker is the one that supplies the missing piece.
StartSmoke ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ i \notin offer
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoke ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \/ StartSmoke
  \/ StopSmoke

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(StopSmoke)

====