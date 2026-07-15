---- MODULE CigaretteSmokers ----
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers
VARIABLE smokers, dealer

(***************************************************************************)
(* 'Ingredients' is a set of ingredients, originally                       *)
(* {matches, paper, tobacco}. 'Offers' is a subset of subsets of           *)
(* ingredients, each missing just one ingredient                           *)
(***************************************************************************)
ASSUME /\ Offers \subseteq SUBSET Ingredients
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from each ingredient to a record that contains   *)
(* a Boolean flag indicating whether the smoker is currently smoking.      *)
(* 'dealer' is either one of the possible offers (a set of two ingredients) *)
(* or the empty set, meaning no offer is currently on the table.             *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking : BOOLEAN]]
          /\ dealer \in Offers \cup {{}}

vars == <<smokers, dealer>>

(***************************************************************************)
(* Helper to pick the unique smoker that is currently smoking, if any.     *)
(***************************************************************************)
UniqueSmoker == 
  CHOOSE r \in Ingredients : smokers[r].smoking

(***************************************************************************)
(* Initialization: all smokers are not smoking and the dealer puts an       *)
(* arbitrary offer on the table.                                            *)
(***************************************************************************)
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* startSmoking: the dealer must have placed an offer (two ingredients).   *)
(* One of the smokers whose ingredient is NOT in the offer starts smoking   *)
(* (i.e., the missing ingredient). The dealer then removes the offer from   *)
(* the table (becomes empty).                                               *)
(***************************************************************************)
startSmoking == 
  /\ dealer # {}
  /\ \E r \in Ingredients :
        /\ r \notin dealer               \* the smoker whose ingredient is missing
        /\ smokers'[r].smoking = TRUE
        /\ \A i \in Ingredients :
               i # r => smokers'[i].smoking = smokers[i].smoking
        /\ dealer' = {}

(***************************************************************************)
(* stopSmoking: there must be exactly one smoker currently smoking. This    *)
(* smoker stops, and the dealer puts a (possibly different) offer back on   *)
(* the table.                                                                *)
(***************************************************************************)
stopSmoking == 
  /\ dealer = {}
  /\ \E r \in Ingredients :
        /\ smokers[r].smoking
        /\ smokers'[r].smoking = FALSE
        /\ \A i \in Ingredients :
               i # r => smokers'[i].smoking = smokers[i].smoking
        /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* An invariant checking that at most one smoker smokes at any particular  *)
(* moment.                                                                   *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1

====