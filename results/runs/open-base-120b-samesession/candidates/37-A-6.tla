---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANT Ingredients
CONSTANT Offers

VARIABLES smoking, offer

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ (offer \in Offers) \/ (offer = {})

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(*-----------------------------------------------------------------
  Action: a smoker starts smoking
-----------------------------------------------------------------*)
StartSmoking ==
    /\ offer # {}
    /\ LET missing == Ingredients \ offer IN
         /\ Cardinality(missing) = 1
         /\ \E i \in missing :
                /\ smoking[i] = FALSE
                /\ smoking' = [smoking EXCEPT ![i] = TRUE]
                /\ offer'   = {}

(*-----------------------------------------------------------------
  Action: the smoking smoker stops and dealer places a new offer
-----------------------------------------------------------------*)
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
           /\ smoking[i] = TRUE
           /\ smoking' = [smoking EXCEPT ![i] = FALSE]
           /\ offer'   \in Offers

Next == StartSmoking \/ StopSmoking

(*-----------------------------------------------------------------
  Specification (includes weak fairness on Next)
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<smoking, offer>> /\ WF_vars(Next)

(*-----------------------------------------------------------------
  Safety invariants
-----------------------------------------------------------------*)
AtMostOne ==
    Cardinality({ i \in Ingredients : smoking[i] }) <= 1

====