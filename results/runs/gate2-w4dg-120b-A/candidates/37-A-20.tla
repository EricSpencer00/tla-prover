---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

RECURSIVE SumF(_, _)
SumF(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumF(f, S \ {x})

\* The smoker holding the missing ingredient is the one who can start; the
\* offer is cleared the moment a smoker begins, so the table is empty while
\* someone smokes -- a reader who looked at the offer during that instant
\* would see nothing offered at all, and must re-check at the next step.
\* The fairness clause below is what keeps the system from stalling forever
\* (for instance on a loop of Start each with the offer empty, or on a loop
\* of Stop each with the offer non-empty but no offer that any smoker can
\* act on -- the latter is ruled out by the model because every offer is
\* missing exactly one ingredient).

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup { {} }

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ \E o \in Offers : offer = o

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
        /\ i \notin offer
        /\ ~smoking[i]
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
        /\ smoking[i]
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ \E o \in Offers : offer' = o

Next ==
    \/ StartSmoking
    \/ StopSmoking

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(StartSmoking)
    /\ WF_vars(StopSmoking)

AtMostOne ==
    SumF(smoking, Ingredients) <= 1

====