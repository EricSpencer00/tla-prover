---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

(* A model of the cigarette smokers problem (Suhas Patil, 1971). The dealer *)
(* offers a subset of the ingredients (missing exactly one); one smoker,     *)
(* each holding an infinite supply of one ingredient, may smoke when the      *)
(* combined ingredients are complete. At most one smoker smokes at a time.    *)

CONSTANTS Ingredients, Offers

Smoker == { i : i \in Ingredients }

VARIABLES smoking, offer
vars == <<smoking, offer>>

TypeOK ==
  /\ smoking \in [Smoker -> BOOLEAN]
  /\ offer \in Offers \cup {{}}

AtMostOne ==
  \A a, b \in Smoker : (smoking[a] /\ smoking[b]) => a = b

Init ==
  /\ smoking = [i \in Smoker |-> FALSE]
  /\ \E o \in Offers : offer = o

StartSmoking ==
  /\ offer # {}
  /\ \E i \in Smoker :
       /\ \A j \in Smoker : j # i => ~smoking[j]
       /\ (offer \cup {i}) = Ingredients
       /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Smoker :
       /\ smoking[i]
       /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ \E o \in Offers : offer' = o

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars
        /\ WF_vars(StartSmoking) /\ WF_vars(StopSmoking)

====