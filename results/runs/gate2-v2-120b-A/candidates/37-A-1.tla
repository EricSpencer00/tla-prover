---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Ingredients, Offers

(* ------------------------------------------------------------------------ *)
(*  State variables                                                         *)
(* ------------------------------------------------------------------------ *)
VARIABLES smokers, offer

(* smokers maps each ingredient to a Boolean indicating whether the smoker
   that owns that ingredient is currently smoking. *)
(* offer is either a non‑empty subset of Ingredients (exactly one ingredient
   missing) or the empty set, which means a smoker is currently smoking. *)

(* ------------------------------------------------------------------------ *)
(*  Helper definitions                                                     *)
(* ------------------------------------------------------------------------ *)
CompleteSet == Ingredients

(* The set of all valid offers: subsets missing exactly one ingredient. *)
ValidOffers == { S \in SUBSET Ingredients : Cardinality(Ingredients \ S) = 1 }

(* The single smoker who is currently smoking, if any. *)
CurrentSmoker == 
  IF offer = {} THEN 
    CHOOSE i \in Ingredients : smokers[i] = TRUE
  ELSE 
    "None"

(* ------------------------------------------------------------------------ *)
(*  Type correctness predicate                                              *)
(* ------------------------------------------------------------------------ *)
TypeOK == 
  /\ smokers \in [Ingredients -> BOOLEAN]
  /\ offer \in SUBSET Ingredients
  /\ (offer = {} => \E i \in Ingredients : smokers[i] = TRUE)
  /\ (offer # {} => \A i \in Ingredients : ~smokers[i])

(* ------------------------------------------------------------------------ *)
(*  Initial state                                                          *)
(* ------------------------------------------------------------------------ *)
Init == 
  /\ smokers = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

(* ------------------------------------------------------------------------ *)
(*  Actions                                                                *)
(* ------------------------------------------------------------------------ *)

(* A smoker whose own ingredient completes the set starts smoking. *)
StartSmoking == 
  /\ offer # {}
  /\ \E i \in Ingredients :
        /\ i \notin offer               \* the missing ingredient belongs to this smoker
        /\ smokers[i] = FALSE
        /\ smokers' = [smokers EXCEPT ![i] = TRUE]
  /\ offer' = {}                        \* table cleared while smoking

(* The currently smoking smoker stops and the dealer puts a new offer. *)
StopSmoking == 
  /\ offer = {}
  /\ smokers[CurrentSmoker] = TRUE
  /\ smokers' = [smokers EXCEPT ![CurrentSmoker] = FALSE]
  /\ offer' \in Offers

Next == 
  \/ StartSmoking
  \/ StopSmoking

(* ------------------------------------------------------------------------ *)
(*  Specification                                                          *)
(* ------------------------------------------------------------------------ *)
Spec == Init /\ [][Next]_<<smokers, offer>>

(* ------------------------------------------------------------------------ *)
(*  Invariant stating at most one smoker is smoking at any moment           *)
(* ------------------------------------------------------------------------ *)
AtMostOne == Cardinality({ i \in Ingredients : smokers[i] }) <= 1

=============================================================================