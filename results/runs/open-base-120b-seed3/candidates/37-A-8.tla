---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

\*--------------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ (offer = {} \/ offer \in Offers)

\*--------------------------------------------------------------------
\* At most one smoker is smoking
\*--------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : smoking[i] }) <= 1

\*--------------------------------------------------------------------
\* Initial state: no smoker is smoking, dealer places a valid offer
\*--------------------------------------------------------------------
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\*--------------------------------------------------------------------
\* Action: a smoker starts smoking
\*--------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ smoking[i] = FALSE
          /\ offer \cup {i} = Ingredients
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ offer'   = {}

\*--------------------------------------------------------------------
\* Action: the current smoker stops and dealer offers a new subset
\*--------------------------------------------------------------------
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ offer'   \in Offers

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\*--------------------------------------------------------------------
\* Specification with weak fairness on Next
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smoking, offer>> /\ WF_vars(Next)

====