---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

(* --type invariants-- *)
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ (offer = {} \/ offer \in Offers)

(* --safety invariant: at most one smoker is smoking-- *)
AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => i = j

(* --initial state-- *)
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* --action: a smoker starts smoking-- *)
StartSmoking(i) ==
    /\ i \in Ingredients
    /\ offer = Ingredients \ {i}
    /\ ~smoking[i]
    /\ \A j \in Ingredients : (j # i) => ~smoking[j]
    /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

(* --action: the smoker stops and dealer places a new offer-- *)
StopSmoking(i) ==
    /\ i \in Ingredients
    /\ offer = {}
    /\ smoking[i]
    /\ \A j \in Ingredients : (j # i) => ~smoking[j]
    /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next ==
    \/ \E i \in Ingredients : StartSmoking(i)
    \/ \E i \in Ingredients : StopSmoking(i)

Spec ==
    Init /\ [][Next]_<<smoking, offer>> /\ WF_<<smoking, offer>>(Next)

====