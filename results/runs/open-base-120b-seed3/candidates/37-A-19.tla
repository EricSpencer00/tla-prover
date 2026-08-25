---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES sm, offer

(*--alias variables for readability*)
vars == << sm, offer >>

(* Type invariant *)
TypeOK ==
    /\ sm \in [Ingredients -> BOOLEAN]
    /\ offer \in (Offers \cup { {} })

(* At most one smoker is smoking *)
AtMostOne ==
    Cardinality({ i \in Ingredients : sm[i] }) <= 1

(* Initial state *)
Init ==
    /\ sm = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* Helper: the ingredient missing from the current offer *)
MissingIngredient(i) ==
    i \notin offer /\ (offer \cup {i}) = Ingredients

(* Start smoking action *)
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ MissingIngredient(i)
          /\ sm[i] = FALSE
          /\ sm' = [sm EXCEPT ![i] = TRUE]
          /\ offer' = {}
          /\ UNCHANGED << >>

(* Stop smoking action *)
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ sm[i] = TRUE
          /\ sm' = [sm EXCEPT ![i] = FALSE]
          /\ offer' \in Offers
          /\ UNCHANGED << >>

Next ==
    StartSmoking \/ StopSmoking

(* Specification with weak fairness on Next *)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

====