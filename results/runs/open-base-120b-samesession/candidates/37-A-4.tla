---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
  /\ Smoking \in [Ingredients -> BOOLEAN]
  /\ Offer \in (Offers \cup {∅})
  /\ ( Offer = ∅ =>
        /\ Cardinality({ i \in Ingredients : Smoking[i] }) = 1 )
  /\ ( Offer # ∅ =>
        /\ \A i \in Ingredients : Smoking[i] = FALSE )

\* ----------------------------------------------------------------------
\* Invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
  Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Smoking = [i \in Ingredients |-> FALSE]
  /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
\* ----------------------------------------------------------------------
StartSmoking ==
  /\ Offer \in Offers
  /\ \E i \in Ingredients :
        /\ Offer = Ingredients \ {i}
        /\ Smoking[i] = FALSE
        /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
        /\ Offer' = ∅

\* ----------------------------------------------------------------------
\* Action: the current smoker stops smoking and dealer offers new set
\* ----------------------------------------------------------------------
StopSmoking ==
  /\ Offer = ∅
  /\ \E i \in Ingredients :
        /\ Smoking[i] = TRUE
        /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
        /\ Offer' \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \/ StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Variables tuple for stuttering and fairness
\* ----------------------------------------------------------------------
vars == <<Smoking, Offer>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====