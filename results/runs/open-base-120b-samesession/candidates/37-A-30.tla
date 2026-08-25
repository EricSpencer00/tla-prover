---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Ingredients, Offers

VARIABLES smokerStatus, Offer

(*--------------------------------------------------------------------
  Type invariant
---------------------------------------------------------------------*)
TypeOK ==
    /\ smokerStatus \in [Ingredients -> BOOLEAN]
    /\ Offer \in (Offers \cup { {} })

(*--------------------------------------------------------------------
  At most one smoker is smoking
---------------------------------------------------------------------*)
AtMostOne ==
    Cardinality({ i \in Ingredients : smokerStatus[i] }) <= 1

(*--------------------------------------------------------------------
  Initial state: no smoker is smoking, dealer places a nondeterministic
  valid offer.
---------------------------------------------------------------------*)
Init ==
    /\ smokerStatus = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(*--------------------------------------------------------------------
  Action: a smoker starts smoking.
  Preconditions:
    – an offer is present (non‑empty);
    – no smoker is currently smoking;
    – the smoker whose ingredient is the unique one missing from the
      offer starts smoking.
---------------------------------------------------------------------*)
StartSmoking ==
    /\ Offer # {}                     \* an offer is on the table
    /\ \A i \in Ingredients : ~smokerStatus[i]   \* nobody is smoking
    /\ \E i \in Ingredients :
          /\ i \notin Offer           \* the missing ingredient
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = TRUE]
          /\ Offer' = {}

(*--------------------------------------------------------------------
  Action: the currently smoking smoker stops and the dealer places a
  new offer.
---------------------------------------------------------------------*)
StopSmoking ==
    /\ Offer = {}                      \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ smokerStatus[i]          \* the smoker that is smoking
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

Next ==
    \/ StartSmoking
    \/ StopSmoking

vars == <<smokerStatus, Offer>>

(*--------------------------------------------------------------------
  Specification: initial condition, next‑state relation, and weak
  fairness on Next.
---------------------------------------------------------------------*)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

====