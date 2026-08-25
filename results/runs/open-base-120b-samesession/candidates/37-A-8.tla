---- MODULE CigaretteSmokers ----
EXTEND FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

(*--------------------------------------------------------------------*)
(*  Helper definition: the set of all ingredients a smoker needs to
    have in order to smoke given the current offer.                     *)
MissingIngredient(offer) ==
    IF offer = {} THEN {} ELSE
        Ingredients \cup {} \ { i \in Ingredients : offer = Ingredients \ {i} }

(*--------------------------------------------------------------------*)
(*  Type invariant                                                    *)
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in Offers

(*--------------------------------------------------------------------*)
(*  Safety: at most one smoker is smoking at any time                 *)
AtMostOne ==
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

(*--------------------------------------------------------------------*)
(*  Initial state                                                     *)
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(*--------------------------------------------------------------------*)
(*  Action: a smoker starts smoking                                    *)
StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ Offer = Ingredients \ {i}
          /\ Smoking[i] = FALSE
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer' = {}

(*--------------------------------------------------------------------*)
(*  Action: the currently smoking smoker stops and dealer offers new  *)
StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers

(*--------------------------------------------------------------------*)
Next ==
    \/ StartSmoking
    \/ StopSmoking

(*--------------------------------------------------------------------*)
(*  Set of all variables                                               *)
vars == <<Smoking, Offer>>

(*--------------------------------------------------------------------*)
(*  Specification                                                     *)
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================