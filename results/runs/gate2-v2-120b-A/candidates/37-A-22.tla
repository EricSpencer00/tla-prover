---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, TLC

(*-------------------------------------------------------------------*)
(*  Constants (will be instantiated in the .cfg file)                *)
(*-------------------------------------------------------------------*)
CONSTANTS Ingredients, Offers

(*-------------------------------------------------------------------*)
(*  Derived sets                                                    *)
(*-------------------------------------------------------------------*)
CompleteSet == Ingredients

(*-------------------------------------------------------------------*)
(*  Variables                                                       *)
(*-------------------------------------------------------------------*)
VARIABLES smoking, offer

(*-------------------------------------------------------------------*)
(*  Type definitions                                                *)
(*-------------------------------------------------------------------*)
SmokingType == [smoker \in Ingredients |-> BOOLEAN]
OfferType    == SUBSET Ingredients

(*-------------------------------------------------------------------*)
(*  Type invariant                                                  *)
(*-------------------------------------------------------------------*)
TypeOK == /\ smoking \in SmokingType
         /\ offer    \in OfferType
         /\ /\ offer = {}
            \/ Len({ i \in Ingredients : i \in offer }) = Cardinality(Ingredients) - 1

(*-------------------------------------------------------------------*)
(*  Initial state                                                   *)
(*-------------------------------------------------------------------*)
Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer    \in Offers

(*-------------------------------------------------------------------*)
(*  Helper predicates                                               *)
(*-------------------------------------------------------------------*)
AllButOneSet(s) ==
  /\ s \subseteq Ingredients
  /\ Cardinality(s) = Cardinality(Ingredients) - 1

CompletesSet(smoker) ==
  LET missing == { i \in Ingredients : i \notin offer } IN
  /\ Cardinality(missing) = 1
  /\ missing = {smoker}

(*-------------------------------------------------------------------*)
(*  Actions                                                         *)
(*-------------------------------------------------------------------*)
StartSmoking ==
  /\ offer # {}
  /\ \E smoker \in Ingredients :
        /\ CompletesSet(smoker)
        /\ smoking' = [smoking EXCEPT ![smoker] = TRUE]
  /\ offer' = {}

StopSmoking ==
  /\ offer = {}
  /\ \E smoker \in Ingredients :
        /\ smoking[smoker] = TRUE
        /\ smoking' = [smoking EXCEPT ![smoker] = FALSE]
  /\ offer' \in Offers

Next ==
  \/ StartSmoking
  \/ StopSmoking

(*-------------------------------------------------------------------*)
(*  Specification                                                   *)
(*-------------------------------------------------------------------*)
Spec == /\ Init
        /\ [][Next]_<<smoking, offer>>

(*-------------------------------------------------------------------*)
(*  Safety invariant: at most one smoker is smoking at any time    *)
(*-------------------------------------------------------------------*)
AtMostOne == Cardinality({ s \in Ingredients : smoking[s] }) <= 1

=============================================================================