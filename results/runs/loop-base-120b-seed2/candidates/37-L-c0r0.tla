---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, offer

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ smokerStatus \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \cup {{}}

(*-----------------------------------------------------------------
  At most one smoker is smoking
-----------------------------------------------------------------*)
AtMostOne ==
    Cardinality({ i \in Ingredients : smokerStatus[i] }) <= 1

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ smokerStatus = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(*-----------------------------------------------------------------
  Helper: the ingredient missing from the current offer
-----------------------------------------------------------------*)
MissingIngredient(off) == Ingredients \ off

(*-----------------------------------------------------------------
  A smoker starts smoking
-----------------------------------------------------------------*)
StartSmoking ==
    /\ offer # {}
    /\ LET missing == MissingIngredient(offer) IN
        /\ Cardinality(missing) = 1
        /\ \E i \in missing :
            /\ smokerStatus[i] = FALSE
            /\ smokerStatus' = [smokerStatus EXCEPT ![i] = TRUE]
            /\ offer' = {}

(*-----------------------------------------------------------------
  The smoker stops smoking and the dealer places a new offer
-----------------------------------------------------------------*)
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
        /\ smokerStatus[i] = TRUE
        /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
        /\ offer' \in Offers

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next == StartSmoking \/ StopSmoking

vars == <<smokerStatus, offer>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====