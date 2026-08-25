---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Ingredients, Offers

VARIABLES smokerState, Offer

(* ---------------------------------------------------------------------- *)
(*  State variables *)
(* ---------------------------------------------------------------------- *)
vars == << smokerState, Offer >>

(* ---------------------------------------------------------------------- *)
(*  Type correctness invariant *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
  /\ smokerState \in [Ingredients -> BOOLEAN]
  /\ Offer \in Offers \/ Offer = {}

(* ---------------------------------------------------------------------- *)
(*  Safety invariant: at most one smoker is smoking *)
(* ---------------------------------------------------------------------- *)
AtMostOne ==
  Cardinality({ i \in Ingredients : smokerState[i] }) <= 1

(* ---------------------------------------------------------------------- *)
(*  Initial state *)
(* ---------------------------------------------------------------------- *)
Init ==
  /\ smokerState = [i \in Ingredients |-> FALSE]
  /\ Offer \in Offers

(* ---------------------------------------------------------------------- *)
(*  Action: a smoker starts smoking *)
(* ---------------------------------------------------------------------- *)
StartSmoking ==
  /\ Offer \in Offers                         \* dealer has placed a valid offer
  /\ LET i == CHOOSE j \in Ingredients : j \notin Offer IN
        /\ smokerState[i] = FALSE
        /\ smokerState' = [smokerState EXCEPT ![i] = TRUE]
        /\ Offer' = {}
  \* (the missing ingredient i is the one that the smoker possesses)

(* ---------------------------------------------------------------------- *)
(*  Action: the currently smoking smoker stops and dealer offers anew *)
(* ---------------------------------------------------------------------- *)
StopSmoking ==
  /\ Offer = {}                               \* a smoker is currently smoking
  /\ ∃ i \in Ingredients : smokerState[i] = TRUE
  /\ LET i == CHOOSE j \in Ingredients : smokerState[j] = TRUE IN
        /\ smokerState' = [smokerState EXCEPT ![i] = FALSE]
        /\ Offer' \in Offers
  \* after the smoker finishes, the dealer puts a new offer

(* ---------------------------------------------------------------------- *)
(*  Next-state relation *)
(* ---------------------------------------------------------------------- *)
Next ==
  \/ StartSmoking
  \/ StopSmoking

(* ---------------------------------------------------------------------- *)
(*  Specification *)
(* ---------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================