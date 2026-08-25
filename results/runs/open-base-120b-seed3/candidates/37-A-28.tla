---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, Offer

(*--------------------------------------------------------------------*)
(*  Helper definitions                                                *)
(*--------------------------------------------------------------------*)

\* the set of smokers that are currently smoking
SmokingSet == { i \in Ingredients : smokerStatus[i] }

(*--------------------------------------------------------------------*)
(*  Type invariants                                                   *)
(*--------------------------------------------------------------------*)

TypeOK ==
  /\ smokerStatus \in [Ingredients -> BOOLEAN]
  /\ Offer \in SUBSET Ingredients
  /\ (Offer = {} \/ Offer \in Offers)

(*--------------------------------------------------------------------*)
(*  Safety invariant: at most one smoker may be smoking               *)
(*--------------------------------------------------------------------*)

AtMostOne ==
  Cardinality(SmokingSet) <= 1

(*--------------------------------------------------------------------*)
(*  Initialization                                                    *)
(*--------------------------------------------------------------------*)

Init ==
  /\ smokerStatus = [i \in Ingredients |-> FALSE]
  /\ Offer \in Offers

(*--------------------------------------------------------------------*)
(*  Actions                                                          *)
(*--------------------------------------------------------------------*)

StartSmoking ==
  /\ Offer # {}
  /\ \E i \in Ingredients :
        /\ Offer = Ingredients \ {i}
        /\ smokerStatus[i] = FALSE
        /\ smokerStatus' = [smokerStatus EXCEPT ![i] = TRUE]
        /\ Offer' = {}

StopSmoking ==
  /\ Offer = {}
  /\ \E i \in Ingredients :
        /\ smokerStatus[i] = TRUE
        /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
        /\ Offer' \in Offers

Next ==
  \/ StartSmoking
  \/ StopSmoking

(*--------------------------------------------------------------------*)
(*  Specification                                                    *)
(*--------------------------------------------------------------------*)

vars == <<smokerStatus, Offer>>

Spec ==
  Init /\
  [][Next]_vars /\
  WF_vars(Next)

(*--------------------------------------------------------------------*)
(*  The identifiers required by the .cfg file                         *)
(*--------------------------------------------------------------------*)

SPECIFICATION Spec
INVARIANT TypeOK
INVARIANT AtMostOne

====