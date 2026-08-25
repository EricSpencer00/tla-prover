---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

(*--variables--*)
VARIABLES Smoking, Offer

(* Type invariant *)
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in (Offers \cup { {} })

(* Initial state *)
Init ==
    /\ TypeOK
    /\ \A i \in Ingredients : Smoking[i] = FALSE
    /\ Offer \in Offers

(* Action: a smoker starts smoking *)
StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
        /\ i \notin Offer               \* the missing ingredient
        /\ Smoking[i] = FALSE
        /\ \A j \in Ingredients : (j # i) => Smoking[j] = FALSE
        /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
        /\ Offer'   = {}

(* Action: the current smoker stops and dealer offers a new set *)
StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
        /\ Smoking[i] = TRUE
        /\ \A j \in Ingredients : (j # i) => Smoking[j] = FALSE
        /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
        /\ Offer'   \in Offers

Next ==
    \/ StartSmoking
    \/ StopSmoking

(* Set of variables for the next-state relation *)
Vars == <<Smoking, Offer>>

(* Specification with weak fairness on Next *)
Spec ==
    Init /\ [] [][Next]_Vars /\ WF_Vars(Next)

(* Safety invariant: at most one smoker is smoking *)
AtMostOne ==
    \A i, j \in Ingredients :
        (Smoking[i] /\ Smoking[j]) => i = j

====