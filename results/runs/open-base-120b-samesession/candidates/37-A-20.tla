---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES SmokerState, Offer

(*--------------------------------------------------------------------
  Type correctness
--------------------------------------------------------------------*)
TypeOK ==
  /\ SmokerState \in [Ingredients -> BOOLEAN]
  /\ (Offer \in Offers \/ Offer = {})

(*--------------------------------------------------------------------
  Invariant: at most one smoker is smoking
--------------------------------------------------------------------*)
AtMostOne ==
  Cardinality({ i \in Ingredients : SmokerState[i] }) <= 1

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ SmokerState = [i \in Ingredients |-> FALSE]
  /\ Offer \in Offers

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
Start(i) ==
  /\ Offer /= {}
  /\ i \in Ingredients
  /\ i \notin Offer               \* the missing ingredient
  /\ SmokerState[i] = FALSE
  /\ SmokerState' = [SmokerState EXCEPT ![i] = TRUE]
  /\ Offer' = {}

Stop(i) ==
  /\ Offer = {}
  /\ i \in Ingredients
  /\ SmokerState[i] = TRUE
  /\ SmokerState' = [SmokerState EXCEPT ![i] = FALSE]
  /\ Offer' \in Offers

Next ==
  \/ \E i \in Ingredients : Start(i)
  \/ \E i \in Ingredients : Stop(i)

vars == <<SmokerState, Offer>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================