---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* Smokers is the set of all subsets of Ingredients that are valid offers --
\* each being just one ingredient short of a complete set.
Smokers == {x \in Offers : Cardinality(Ingredients \ x) = 1}

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {{})

Init ==
  /\ \A g \in Ingredients : ~smoking[g]
  /\ offer \in Smokers

\* A single smoker, whose own ingredient completes the full set, starts
\* smoking. The offer is cleared exactly as smoking begins.
StartSmoking ==
  /\ offer # {}
  /\ \E g \in Ingredients :
       /\ g \notin offer
       /\ smoking[g] = FALSE
       /\ smoking' = [smoking EXCEPT ![g] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E g \in Ingredients :
       /\ smoking[g]
       /\ smoking' = [smoking EXCEPT ![g] = FALSE]
  /\ \E h \in Smokers : offer' = h

Next ==
  \/ StartSmoking
  \/ StopSmoking

Spec == Init /\ [][Next]_vars

\* At most one smoker is ever smoking at the same time.
AtMostOne == \A g1, g2 \in Ingredients : (smoking[g1] /\ smoking[g2]) => g1 = g2

\* Progress: the system never stalls -- some smoker always eventually smokes
\* and then stops again.
SF == WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

====