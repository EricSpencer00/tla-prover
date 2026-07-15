---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Ingredients, Offers

(* Set of all possible states of the system *)
VARIABLES smoking, offer

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------- *)

(* The set of all possible offers must be a subset of the power set of Ingredients
   and each offer must miss exactly one ingredient.  This invariant is checked
   in TypeOK. *)
AllOffersOK == 
    /\ \A o \in Offers: o \subseteq Ingredients
    /\ \A o \in Offers: Cardinality(Ingredients \ o) = 1

(* ------------------------------------------------------------------------- *)
(* Initial predicate                                                        *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

(* ------------------------------------------------------------------------- *)
(* Actions                                                                  *)
(* ------------------------------------------------------------------------- *)

(* A smoker whose ingredient i completes the set starts smoking. *)
StartSmoking ==
    /\ offer \in Offers               \* there is an offer on the table
    /\ \E i \in Ingredients :
          /\ i \notin offer            \* i is the missing ingredient
          /\ smoking[i] = FALSE
          /\ \A j \in Ingredients :
                (j # i) => smoking[j] = FALSE   \* no other smoker is smoking
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

(* The currently smoking smoker stops and the dealer places a new offer. *)
StopSmoking ==
    /\ offer = {}                     \* no offer means someone is smoking
    /\ \E i \in Ingredients :
          /\ smoking[i] = TRUE
          /\ ~\E j \in Ingredients : (j # i) /\ smoking[j] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

(* ------------------------------------------------------------------------- *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<smoking, offer>>

(* ------------------------------------------------------------------------- *)
(* Type correctness invariant                                               *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in {EMPTYSET} \cup Offers
    /\ AllOffersOK

(* ------------------------------------------------------------------------- *)
(* Safety invariant: at most one smoker is smoking at any time             *)
(* ------------------------------------------------------------------------- *)

AtMostOne == Cardinality({ i \in Ingredients : smoking[i] }) <= 1

=============================================================================