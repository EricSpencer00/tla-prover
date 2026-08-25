---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, offer

(* tuple of all variables *)
vars == <<smokerStatus, offer>>

(* a valid offer is a subset of Ingredients that is missing exactly one ingredient *)
IsValidOffer(o) ==
  /\ o \in Offers
  /\ Cardinality(o) = Cardinality(Ingredients) - 1
  /\ o \subseteq Ingredients

(* Type correctness invariant *)
TypeOK ==
  /\ smokerStatus \in [Ingredients -> BOOLEAN]
  /\ offer \in SUBSET Ingredients
  /\ (offer = {} \/ IsValidOffer(offer))

(* Safety invariant: at most one smoker is smoking *)
AtMostOne ==
  Cardinality({ i \in Ingredients : smokerStatus[i] }) <= 1

(* Initial state: no one is smoking, dealer places a nondeterministic valid offer *)
Init ==
  /\ smokerStatus = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

(* Action: a smoker whose missing ingredient completes the set begins to smoke *)
StartSmoking ==
  /\ offer # {}
  /\ \E i \in Ingredients :
        /\ i \notin offer
        /\ offer = Ingredients \ {i}
        /\ smokerStatus[i] = FALSE
        /\ smokerStatus' = [smokerStatus EXCEPT ![i] = TRUE]
        /\ offer' = {}

(* Action: the currently smoking smoker stops and dealer puts a new offer *)
StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
        /\ smokerStatus[i] = TRUE
        /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
        /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

(* Specification with weak fairness of Next *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====