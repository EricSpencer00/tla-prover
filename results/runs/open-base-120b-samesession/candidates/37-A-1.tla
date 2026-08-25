---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, Offer

(* ----------------------------------------------------------------------
   Type constraints
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer = {} \/ Offer \in Offers)

(* ----------------------------------------------------------------------
   Initial state: no smoker is smoking and the dealer places a valid offer
   ---------------------------------------------------------------------- *)
Init ==
    /\ TypeOK
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ Offer \in Offers

(* ----------------------------------------------------------------------
   An individual smoker starts smoking
   ---------------------------------------------------------------------- *)
Start(i) ==
    /\ i \in Ingredients
    /\ Offer = Ingredients \ {i}
    /\ smoking[i] = FALSE
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ Offer'   = {}
    /\ UNCHANGED << >>

(* ----------------------------------------------------------------------
   The smoking smoker stops and the dealer places a new offer
   ---------------------------------------------------------------------- *)
Stop(i) ==
    /\ i \in Ingredients
    /\ Offer = {}
    /\ smoking[i] = TRUE
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ Offer'   \in Offers
    /\ UNCHANGED << >>

(* ----------------------------------------------------------------------
   Next-state relation
   ---------------------------------------------------------------------- *)
Next ==
    \/ \E i \in Ingredients : Start(i)
    \/ \E i \in Ingredients : Stop(i)

vars == <<smoking, Offer>>

(* ----------------------------------------------------------------------
   Specification (includes weak fairness on Next)
   ---------------------------------------------------------------------- *)
Spec == Init /\ [] [Next]_vars /\ WF_vars(Next)

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)
TypeOK   == TypeOK
AtMostOne ==
    SetCard({ i \in Ingredients : smoking[i] }) <= 1

====