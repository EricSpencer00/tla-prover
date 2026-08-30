---- MODULE CigaretteSmokers ----
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

\* Each smoker is the holder of exactly one distinct ingredient from Ingredients.
\* Exactly one smoker may be smoking at any time; the dealer is never slow, only
\* slow-to-act, so the fairness constraints below are what force progress.
VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (SUBSET Ingredients) \cup {{}}

AtMostOne == \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => i = j

\* The offer is a subset of ingredients missing exactly one; smoking is a
\* boolean per-ingredient flag rather than a single holder, so the invariant is
\* the only thing keeping two smokers from both claiming to be smoking.
Init ==
  /\ \A i \in Ingredients : smoking[i] = FALSE
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
       /\ offer \cup {i} = Ingredients
       /\ smoking[i] = FALSE
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
       /\ smoking[i] = TRUE
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
    /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

TypeOKInv == TypeOK
====