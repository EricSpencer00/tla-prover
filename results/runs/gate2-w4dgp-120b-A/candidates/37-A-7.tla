---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

\* Each smoker has an infinite supply of exactly one ingredient, and smokes when
\* the dealer's offer (a subset missing exactly one ingredient) plus that
\* ingredient gives the full set. The dealer waits for the smoker to finish
\* before placing a new offer, so at most one smoker smokes at a time.

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

\* The dealer's offer names the missing ingredient; the smoker who owns it
\* starts smoking and the offer is cleared while a smoker smokes.
StartSmoking(i) ==
  /\ offer # {}
  /\ ~smoking[i]
  /\ \A j \in Ingredients : ~smoking[j]
  /\ \A j \in Ingredients : j # i => j \in offer
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

\* When the table is clear (a smoker is smoking), that smoker stops and the
\* dealer places a new offer, chosen nondeterministically from the valid set.
StopSmoking(i) ==
  /\ smoking[i]
  /\ \A j \in Ingredients : ~smoking[j]
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next ==
  \E i \in Ingredients : StartSmoking(i) \/ StopSmoking(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

\* Nobody smokes unless the dealer's offer is exactly the missing ingredient.
AtMostOne ==
  \A i \in Ingredients :
    smoking[i] => \A j \in Ingredients : (j # i => j \in offer)

====