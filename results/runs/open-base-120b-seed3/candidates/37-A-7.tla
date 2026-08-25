---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, currentOffer

(* --------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ currentOffer \in SUBSET Ingredients

(* --------------------------------------------------------------------- *)
(* Helper sets *)
SmokingSet == { i \in Ingredients : smoking[i] }

(* --------------------------------------------------------------------- *)
(* Safety invariant: at most one smoker is smoking *)
AtMostOne ==
    Cardinality(SmokingSet) <= 1

(* --------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ currentOffer \in Offers

(* --------------------------------------------------------------------- *)
(* Action: a smoker starts smoking *)
Start ==
    /\ currentOffer # {}
    /\ \E i \in Ingredients :
          /\ i \notin currentOffer              \* the missing ingredient
          /\ smoking[i] = FALSE
          /\ \A j \in Ingredients : (j # i) => smoking[j] = FALSE
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ currentOffer' = {}

(* --------------------------------------------------------------------- *)
(* Action: the currently smoking smoker stops and dealer offers new set *)
Stop ==
    /\ currentOffer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ currentOffer' \in Offers

(* --------------------------------------------------------------------- *)
Next == \/ Start \/ Stop

vars == <<smoking, currentOffer>>

(* --------------------------------------------------------------------- *)
(* Specification with weak fairness on Next *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================