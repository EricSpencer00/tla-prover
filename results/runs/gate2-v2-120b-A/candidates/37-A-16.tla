---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Ingredients, Offers

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES Smoking, CurrentOffer

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
CompleteSet == Ingredients

ValidOffer(offer) == 
    /\ offer \in Offers
    /\ Len(offer) = Cardinality(Ingredients) - 1
    /\ offer \subseteq Ingredients

(*--------------------------------------------------------------------
  Types for TypeOK invariant
--------------------------------------------------------------------*)
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ CurrentOffer \in Offers

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ \E initOffer \in Offers : 
         /\ ValidOffer(initOffer)
         /\ CurrentOffer = initOffer

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)

(* A smoker whose ingredient is the missing one starts smoking *)
StartSmoking ==
    /\ CurrentOffer # {}
    /\ \E i \in Ingredients :
          /\ i \notin CurrentOffer
          /\ Smoking[i] = FALSE
          /\ \A j \in Ingredients : (j # i) => Smoking[j] = FALSE
          /\ Smoking' = [ Smoking EXCEPT ![i] = TRUE ]
    /\ CurrentOffer' = {}

(* The currently smoking smoker stops and dealer places a new offer *)
StopSmoking ==
    /\ CurrentOffer = {}
    /\ \E i \in Ingredients :
          /\ Smoking[i] = TRUE
          /\ \A j \in Ingredients : (j # i) => Smoking[j] = FALSE
    /\ \E newOffer \in Offers :
          /\ ValidOffer(newOffer)
          /\ Smoking' = [ Smoking EXCEPT ![i] = FALSE ]
          /\ CurrentOffer' = newOffer

Next == StartSmoking \/ StopSmoking

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<Smoking, CurrentOffer>>

(*--------------------------------------------------------------------
  Safety invariant: at most one smoker is smoking
--------------------------------------------------------------------*)
AtMostOne ==
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

====