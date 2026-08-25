---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllowedOffers == Offers \cup { {} }

MissingIngredient(offer) == 
  CHOOSE i \in Ingredients : i \notin offer

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK == 
  /\ Smoking \in [Ingredients -> BOOLEAN]
  /\ Offer \in AllowedOffers

\* ----------------------------------------------------------------------
\* Safety: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne == 
  Cardinality({ i \in Ingredients : Smoking[i] }) \le 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
  /\ Smoking = [i \in Ingredients |-> FALSE]
  /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking == 
  /\ Offer \in Offers
  /\ \E i \in Ingredients :
        /\ i \notin Offer               \* the missing ingredient
        /\ Smoking[i] = FALSE
        /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
        /\ Offer' = {}

StopSmoking == 
  /\ Offer = {}
  /\ \E i \in Ingredients :
        /\ Smoking[i] = TRUE
        /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
        /\ Offer' \in Offers

Next == \/ StartSmoking
        \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Smoking, Offer>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* SPECIFICATION   Spec
\* INVARIANT       TypeOK
\* INVARIANT       AtMostOne

====