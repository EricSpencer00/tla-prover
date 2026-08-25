---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smoke, offer

(* --- Type invariant --------------------------------------------------- *)
TypeOK ==
    /\ smoke \in [Ingredients -> BOOLEAN]
    /\ (offer = {} \/ offer \in Offers)

(* --- Helper definitions ------------------------------------------------ *)
MissingSet(off) == Ingredients \ off

(* --- Actions ----------------------------------------------------------- *)

StartSmoking ==
    /\ offer # {}
    /\ Cardinality(MissingSet(offer)) = 1
    /\ LET i == THE MissingSet(offer) IN
           /\ smoke' = [smoke EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ Cardinality({ i \in Ingredients : smoke[i] }) = 1
    /\ LET i == THE { i \in Ingredients : smoke[i] } IN
           /\ smoke' = [smoke EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next ==
    \/ StartSmoking
    \/ StopSmoking

(* --- Initialization ---------------------------------------------------- *)

Init ==
    /\ smoke = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

vars == <<smoke, offer>>

(* --- Specification ------------------------------------------------------ *)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

(* --- Invariants -------------------------------------------------------- *)

AtMostOne ==
    Cardinality({ i \in Ingredients : smoke[i] }) <= 1

====