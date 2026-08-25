---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

(* Tuple of all variables, used in the stuttering action *)
Vars == <<smoking, offer>>

(* ------------------------------------------------------------------- *)
(* Type correctness predicate                                            *)
(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in SUBSET Ingredients

(* ------------------------------------------------------------------- *)
(* Initial state                                                         *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* ------------------------------------------------------------------- *)
(* Action: a smoker starts smoking                                       *)
(* ------------------------------------------------------------------- *)
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
        /\ offer = Ingredients \ {i}
        /\ smoking[i] = FALSE
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
        /\ offer' = {}

(* ------------------------------------------------------------------- *)
(* Action: the current smoker stops and the dealer places a new offer    *)
(* ------------------------------------------------------------------- *)
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
        /\ smoking[i] = TRUE
        /\ \A j \in Ingredients : (j # i) => smoking[j] = FALSE
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
        /\ offer' \in Offers

(* ------------------------------------------------------------------- *)
(* Next-state relation                                                   *)
(* ------------------------------------------------------------------- *)
Next == StartSmoking \/ StopSmoking

(* ------------------------------------------------------------------- *)
(* Specification with weak fairness                                      *)
(* ------------------------------------------------------------------- *)
Spec ==
    Init /\ [][Next]_Vars /\ WF_vars(Next)

(* ------------------------------------------------------------------- *)
(* Invariant: at most one smoker is smoking                               *)
(* ------------------------------------------------------------------- *)
AtMostOne ==
    \A i, j \in Ingredients : (i # j) => ~(smoking[i] /\ smoking[j])

====