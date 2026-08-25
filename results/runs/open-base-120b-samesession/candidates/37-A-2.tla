---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer = {} \/ Offer \in Offers)

\* ----------------------------------------------------------------------
\* Safety: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    \A i, j \in Ingredients :
        (Smoking[i] /\ Smoking[j]) => i = j

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers   \* a nondeterministic valid offer

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer # {}                         \* there is an offer on the table
    /\ \E i \in Ingredients :
          /\ i \notin Offer                \* the missing ingredient
          /\ ~Smoking[i]                   \* this smoker is not already smoking
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer' = {}
          /\ \A j \in Ingredients : (j # i) => Smoking'[j] = Smoking[j]

StopSmoking ==
    /\ Offer = {}                         \* a smoker is currently smoking
    /\ \E i \in Ingredients : Smoking[i]   \* the (unique) smoking smoker
    /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
    /\ Offer' \in Offers
    /\ \A j \in Ingredients : (j # i) => Smoking'[j] = Smoking[j]

Next ==
    \/ StartSmoking
    \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Smoking, Offer>>

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Assumptions about the constants (optional, can be omitted if supplied by cfg)
\* ----------------------------------------------------------------------
ASSUME
    /\ Ingredients # {}
    /\ \A o \in Offers :
          /\ o \subseteq Ingredients
          /\ \E missing \in Ingredients :
                /\ missing \notin o
                /\ \A x \in Ingredients : (x \notin o) => x = missing

=============================================================================