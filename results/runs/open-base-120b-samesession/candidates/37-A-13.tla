---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANT Ingredients, Offers

VARIABLES smoking, offer

(* Type invariant *)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (Offers \cup {{} })

(* Initial state *)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* Action: a smoker starts smoking *)
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ i \notin offer
          /\ smoking[i] = FALSE
          /\ /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ offer' = {}

(* Action: the currently smoking smoker stops and dealer puts new offer *)
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients : smoking[i] = TRUE
    /\ /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next ==
    \/ StartSmoking
    \/ StopSmoking

(* Safety: at most one smoker is smoking *)
AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => i = j

Spec ==
    Init /\ [][Next]_<<smoking, offer>> /\ WF_vars(Next)

====