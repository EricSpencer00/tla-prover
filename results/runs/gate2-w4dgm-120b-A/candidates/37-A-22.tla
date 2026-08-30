---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Premises: each smoker holds an infinite supply of exactly one distinct
\* ingredient, so the per-ingredient boolean is enough to identify them.
\* The offer is a subset of Ingredients, and it is always missing exactly one.

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ (offer = {} \/ (offer \subseteq Ingredients /\ Cardinality(offer) = Cardinality(Ingredients) - 1))

Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ ~smoking[i]
       /\ \A j \in Ingredients : (j # i => j \in offer)
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars /\ WF_vars(StopSmoking)

AtMostOne == Cardinality({i \in Ingredients : smoking[i]}) <= 1

TypeOKInv == TypeOK
====