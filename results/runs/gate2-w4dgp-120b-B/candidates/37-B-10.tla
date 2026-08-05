---- MODULE CigaretteSmokers ----
(***************************************************************************)
(* A specification of the cigarette smokers problem, originally            *)
(* described in 1971 by Suhas Patil.                                       *)
(* https://en.wikipedia.org/wiki/Cigarette_smokers_problem                 *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANT Ingredients, Offers

(***************************************************************************)
(* 'Ingredients' is a set of ingredients, originally                       *)
(* {matches, paper, tobacco}. 'Offers' is a subset of subsets of           *)
(* ingredients, each missing just one ingredient                           *)
(***************************************************************************)
ASSUME /\ Offers \subseteq (SUBSET Ingredients)
       /\ \A n \in Offers : Cardinality(n) = Cardinality(Ingredients) - 1

(***************************************************************************)
(* 'smokers' is a function from the ingredient the smoker has              *)
(* infinite supply of, to a record holding the smoker's smoking state       *)
(* 'dealer' is an element of 'Offers', or an empty set                       *)
(***************************************************************************)
TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer  \in Offers \/ dealer = {}

vars == <<smokers, dealer>>

Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers

(***************************************************************************)
(* A smoker is seated and given the missing ingredients, so exactly one     *)
(* smoker smokes at a time, and the table is cleared afterwards              *)
(***************************************************************************)
StartSmoking == /\ dealer /= {}
                 /\ smokers' = [r \in Ingredients |-> [smoking |-> r \in dealer]]
                 /\ dealer' \in Offers
                 
StopSmoking == /\ dealer = {}
                /\ \E r \in Ingredients :
                     /\ smokers[r].smoking
                     /\ smokers' = [smokers EXCEPT ![r].smoking = FALSE]
                /\ dealer' \in Offers
                     /\ dealer' # {}

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* At most one smoker smokes at any one moment                              *)
(***************************************************************************)
AtMostOne == Cardinality({r \in Ingredients : smokers[r].smoking}) <= 1
====