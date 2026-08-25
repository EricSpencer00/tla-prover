---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

\*-------------------------------------------------
\* Type invariant
\*-------------------------------------------------
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in SUBSET Ingredients

\*-------------------------------------------------
\* Initial state
\*-------------------------------------------------
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\*-------------------------------------------------
\* Helper definitions
\*-------------------------------------------------
Missing == Ingredients \ offer

\*-------------------------------------------------
\* Start smoking: a smoker whose ingredient is the missing one begins
\*-------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ Cardinality(Missing) = 1
    /\ \E i \in Missing :
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ offer'   = {}

\*-------------------------------------------------
\* Stop smoking: the currently smoking smoker finishes and a new offer appears
\*-------------------------------------------------
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ offer'   \in Offers

\*-------------------------------------------------
\* Next-state relation
\*-------------------------------------------------
Next ==
    \/ StartSmoking
    \/ StopSmoking

\*-------------------------------------------------
\* Specification
\*-------------------------------------------------
Spec == Init /\ [][Next]_<<smoking, offer>>

\*-------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\*-------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : smoking[i] }) <= 1

\*-------------------------------------------------
\* Assumptions about the constants (optional but useful)
\*-------------------------------------------------
ASSUME
    /\ Offers \subseteq SUBSET Ingredients
    /\ \A o \in Offers : Cardinality(Ingredients \ o) = 1

====