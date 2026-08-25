---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC, Temporal

CONSTANTS Ingredients, Offers

VARIABLES SmokerState, Offer

(* Type invariant for the state variables *)
TypeOK ==
    /\ SmokerState \in [Ingredients -> BOOLEAN]
    /\ Offer \in (Offers \cup { {} })

(* At most one smoker may be smoking at any time *)
AtMostOne ==
    Cardinality({ i \in Ingredients : SmokerState[i] }) <= 1

(* Initial state: no smoker is smoking, dealer places a nondeterministic offer *)
Init ==
    /\ SmokerState = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(* Action: the smoker whose missing ingredient starts smoking *)
StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ i \notin Offer
          /\ SmokerState' = [SmokerState EXCEPT ![i] = TRUE]
          /\ Offer' = {}

(* Action: the current smoker stops and dealer places a new offer *)
StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ SmokerState[i]
          /\ SmokerState' = [SmokerState EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

Next ==
    \/ StartSmoking
    \/ StopSmoking

vars == << SmokerState, Offer >>

Spec ==
    Init /\ [] [Next]_vars /\ WF_vars(Next)

====