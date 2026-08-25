---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, Naturals

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, offer

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

AllIngredients == Ingredients

ValidOffer(o) == o \in Offers /\ Cardinality(AllIngredients \ o) = 1

vars == << smokerStatus, offer >>

(* ----------------------------------------------------------------------
   Type correctness
   ---------------------------------------------------------------------- *)

TypeOK ==
    /\ smokerStatus \in [Ingredients -> BOOLEAN]
    /\ (offer = {} \/ offer \in Offers)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ smokerStatus = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ ~smokerStatus[i]
          /\ (offer \cup {i}) = AllIngredients
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = TRUE]
          /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smokerStatus[i]
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
          /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

AtMostOne ==
    Cardinality({ i \in Ingredients : smokerStatus[i] }) <= 1

====